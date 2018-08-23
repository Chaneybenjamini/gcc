#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "target.h"
#include "tree.h"
#include "tree-iterator.h"
#include "gimple-expr.h"
#include "diagnostic.h"
#include "opts.h"
#include "fold-const.h"
#include "gimplify.h"
#include "stor-layout.h"
#include "debug.h"
#include "convert.h"
#include "langhooks.h"
#include "langhooks-def.h"
#include "common/common-target.h"
#include "stringpool.h"
#include "cgraph.h"

#include <stack>

static tree brainfuck_compile_char(location_t current_location, FILE *input_file, tree super_context, char compiling, tree ptr_decl, tree array_decl);

struct GTY (()) lang_type
{
	char dummy;
};

struct GTY (()) lang_decl
{
	char dummy;
};

struct GTY (()) lang_identifier{
	struct tree_identifier common;
};

union GTY((desc ("TREE_CODE (&%h.generic) == IDENTIFIER_NODE"),
	   chain_next ("CODE_CONTAINS_STRUCT (TREE_CODE (&%h.generic), "
		       "TS_COMMON) ? ((union lang_tree_node *) TREE_CHAIN "
		       "(&%h.generic)) : NULL"))) lang_tree_node
{
	union tree_node GTY((tag ("0"), desc ("tree_node_structure (&%h)"))) generic;
	struct lang_identifier GTY((tag ("1"))) identifier;
};

struct GTY (()) language_function
{
	int dummy;
};

static bool brainfuck_langhooks_init(){
	build_common_tree_nodes(false);
	
	void_list_node = build_tree_list(NULL_TREE, void_type_node);

	build_common_builtin_nodes();

	return true;
}

static tree get_printfn(){
	tree fndecl_type_param[] = {
                integer_type_node
                };
        tree fndecl_type = build_function_type_array (integer_type_node, 1, fndecl_type_param);

        tree printf_fn_decl = build_fn_decl ("putchar", fndecl_type);
        DECL_EXTERNAL(printf_fn_decl) = 1;
        tree print_fn = build1(ADDR_EXPR, build_pointer_type (fndecl_type), printf_fn_decl);
        return print_fn;
}

static tree get_readfn(){
	tree fndecl_type_param[] = {
                };
        tree fndecl_type = build_function_type_array (integer_type_node, 0, fndecl_type_param);

        tree read_fn_decl = build_fn_decl ("getchar", fndecl_type);
        DECL_EXTERNAL(read_fn_decl) = 1;
        tree read_fn = build1(ADDR_EXPR, build_pointer_type (fndecl_type), read_fn_decl);
        return read_fn;
}

static tree brainfuck_create_write(location_t current_loc, tree print_val){
	tree print_fn = get_printfn();
	tree args[] = {print_val};

	tree ret = build_call_array_loc(current_loc, integer_type_node, print_fn, 1, args);
	return ret;
}

static void brainfuck_do_fake_parse(){
	tree main_fndecl_type_param[] = {integer_type_node, build_pointer_type(build_pointer_type(char_type_node))};
	tree main_fndecl_type = build_function_type_array(integer_type_node, 2, main_fndecl_type_param);
	tree main_fndecl = build_fn_decl ("main", main_fndecl_type);
	tree list = alloc_stmt_list();
	tree expr = build_int_cst_type(integer_type_node, 42);
	tree printf_fn = get_printfn();
	tree args[] = {expr};
	tree stmt = build_call_array_loc(UNKNOWN_LOCATION, integer_type_node, printf_fn, 1, args);
	append_to_statement_list(stmt, &list);
	tree resdecl = build_decl(UNKNOWN_LOCATION, RESULT_DECL, NULL_TREE, integer_type_node);
	DECL_CONTEXT(resdecl) = main_fndecl;
	DECL_RESULT(main_fndecl) = resdecl;
	tree set_result = build2(INIT_EXPR, void_type_node, DECL_RESULT(main_fndecl), build_int_cst_type(integer_type_node, 0));
	tree return_stmt = build1(RETURN_EXPR, void_type_node, set_result);
	append_to_statement_list(return_stmt, &list);
	tree new_block = build_block(NULL_TREE, list, NULL_TREE, NULL_TREE);
	tree bind_expr = build3(BIND_EXPR, void_type_node, NULL_TREE, list, new_block);
	BLOCK_SUPERCONTEXT(new_block) = main_fndecl;
	DECL_INITIAL(main_fndecl) = new_block;
	DECL_SAVED_TREE(main_fndecl) = bind_expr;
	DECL_EXTERNAL(main_fndecl) = 0;
	DECL_PRESERVE_P(main_fndecl) = 1;

	gimplify_function_tree(main_fndecl);
	cgraph_node::finalize_function(main_fndecl, true);

}

int current_line = 1;
int current_column = 1;

location_t get_current_location(){
	return linemap_position_for_column(line_table, current_column);
}

static tree brainfuck_compile_scope(FILE *input_file, tree super_context, tree ptr_decl, tree array_decl, bool top_scope){
	int current_char;
	tree stmt_list = alloc_stmt_list();
	location_t start_location = get_current_location();
	while((current_char = getc(input_file)) != -1){
		current_column++;
		if(current_char == '\n'){
			current_column = 1;
			current_line++;
			linemap_line_start(line_table, current_line, 100);
		}
		location_t current_location = get_current_location();
		tree adding = brainfuck_compile_char(current_location, input_file, super_context, current_char, ptr_decl, array_decl);
		if(adding == NULL_TREE){
			if(top_scope)
				error_at(current_location, "unmatched right bracket\n");
			return stmt_list;
		}
		else
			append_to_statement_list(adding, &stmt_list);
	}
	if(!top_scope)
		error_at(start_location, "unmatched left bracket\n");
	return stmt_list;
}

static tree brainfuck_compile_char(location_t current_location, FILE *input_file, tree super_context, char compiling, tree ptr_decl, tree array_decl){
	tree resolve_op, do_op, array_access, fncall;
	tree loop_check, loop_start, loop_end;
	tree check_expr, start_expr, end_expr;
	tree new_stmt_list, inner_scope;
	location_t old_location;
	switch (compiling)
	{
		case '>':
			do_op = build2_loc(current_location, PLUS_EXPR, integer_type_node, ptr_decl, build_int_cst_type(integer_type_node, 1));
			resolve_op = build2_loc(current_location, MODIFY_EXPR, void_type_node, ptr_decl, do_op);
			return resolve_op;
		case '<':
			do_op = build2_loc(current_location, MINUS_EXPR, integer_type_node, ptr_decl, build_int_cst_type(integer_type_node, 1));
			resolve_op = build2_loc(current_location, MODIFY_EXPR, void_type_node, ptr_decl, do_op);
			return resolve_op;
		case '+':
			array_access = build4_loc(current_location, ARRAY_REF, integer_type_node, array_decl, ptr_decl, NULL_TREE, NULL_TREE);
			do_op = build2_loc(current_location, PLUS_EXPR, integer_type_node, array_access, build_int_cst_type(integer_type_node, 1));
			resolve_op = build2_loc(current_location, MODIFY_EXPR, void_type_node, array_access, do_op);
			return resolve_op;
		case '-':
			array_access = build4_loc(current_location, ARRAY_REF, integer_type_node, array_decl, ptr_decl, NULL_TREE, NULL_TREE);
			do_op = build2_loc(current_location, MINUS_EXPR, integer_type_node, array_access, build_int_cst_type(integer_type_node, 1));
			resolve_op = build2_loc(current_location, MODIFY_EXPR, void_type_node, array_access, do_op);
			return resolve_op;
		case '.':
			fncall = get_printfn();
			array_access = build4_loc(current_location, ARRAY_REF, integer_type_node, array_decl, ptr_decl, NULL_TREE, NULL_TREE);
			resolve_op = build_call_array_loc(current_location, integer_type_node, fncall, 1, &array_access);
			return resolve_op;
		case ',':
			fncall = get_readfn();
			array_access = build4_loc(current_location, ARRAY_REF, integer_type_node, array_decl, ptr_decl, NULL_TREE, NULL_TREE);
			do_op = build_call_array_loc(current_location, integer_type_node, fncall, 0, {});
			resolve_op = build2_loc(current_location, MODIFY_EXPR, void_type_node, array_access, do_op);
			return resolve_op;
		case '[':
			new_stmt_list = alloc_stmt_list();
			
			loop_check = build_decl(current_location, LABEL_DECL, get_identifier("loop_check"), void_type_node);
			check_expr = build1_loc(current_location, LABEL_EXPR, void_type_node, loop_check);
			DECL_CONTEXT(loop_check) = super_context;
			loop_start = build_decl(current_location, LABEL_DECL, get_identifier("loop_start"), void_type_node);
			start_expr = build1_loc(current_location, LABEL_EXPR, void_type_node, loop_start);
			DECL_CONTEXT(loop_start) = super_context;
			array_access = build4_loc(current_location, ARRAY_REF, integer_type_node, array_decl, ptr_decl, NULL_TREE, NULL_TREE);
			do_op = build2_loc(current_location, EQ_EXPR, boolean_type_node, array_access,  build_int_cst_type(integer_type_node, 0));
			
			inner_scope = brainfuck_compile_scope(input_file, super_context, ptr_decl, array_decl, false);
			old_location = current_location;
			current_location = get_current_location();

			loop_end = build_decl(current_location, LABEL_DECL, get_identifier("loop_end"), void_type_node);
			end_expr = build1_loc(current_location, LABEL_EXPR, void_type_node, loop_end);
			DECL_CONTEXT(loop_end) = super_context;
			resolve_op = build3_loc(old_location, COND_EXPR, void_type_node, do_op,
				build1_loc(old_location, GOTO_EXPR, void_type_node, loop_end),
				build1_loc(old_location, GOTO_EXPR, void_type_node, loop_start));
			append_to_statement_list(check_expr, &new_stmt_list);
			append_to_statement_list(resolve_op, &new_stmt_list);
			append_to_statement_list(start_expr, &new_stmt_list);
			append_to_statement_list(inner_scope, &new_stmt_list);
			append_to_statement_list(build1_loc(current_location, GOTO_EXPR, void_type_node, loop_check), &new_stmt_list);
			append_to_statement_list(end_expr, &new_stmt_list);

			return new_stmt_list;

		case ']':
			return NULL_TREE;
		default:
			//Anything that isn't one of they key characters is a comment
			return alloc_stmt_list();
	}
}

static void brainfuck_do_parse_file(const char *filename){
	FILE *file = fopen(filename, "r");
	if (file == NULL)
	{
		fatal_error (UNKNOWN_LOCATION, "cannot open filename %s: %m", filename);
	}
	
	tree main_fndecl_type = build_function_type_array (integer_type_node, 0, {});
	tree main_fndecl = build_fn_decl ("main", main_fndecl_type);
	tree stmt_list = alloc_stmt_list();
	
	location_t current_location = UNKNOWN_LOCATION;
	tree ptr_decl = build_decl(current_location, VAR_DECL, get_identifier("ptr"), integer_type_node);
	DECL_CONTEXT(ptr_decl) = main_fndecl;
	tree ptr_stmt = build1_loc(current_location, DECL_EXPR, void_type_node, ptr_decl);
	append_to_statement_list(ptr_stmt, &stmt_list);
	
	tree array_range_type = build_range_type(integer_type_node, build_int_cst_type(integer_type_node, 0), build_int_cst_type(integer_type_node, 30000));
	tree array_type = build_array_type (integer_type_node, array_range_type);
	tree array_decl = build_decl (current_location, VAR_DECL, get_identifier("array"), array_type);
	DECL_CONTEXT(array_decl) = main_fndecl; 
	tree array_stmt = build1_loc(current_location, DECL_EXPR, void_type_node, array_decl);
	append_to_statement_list(array_stmt, &stmt_list);	
	TREE_CHAIN(ptr_decl) = array_decl;

	tree ptr_init = build2_loc(UNKNOWN_LOCATION, INIT_EXPR, void_type_node, ptr_decl, build_int_cst_type(integer_type_node, 0));
	append_to_statement_list(ptr_init, &stmt_list);
	
	tree current_block = build_block(ptr_decl, NULL_TREE, main_fndecl, NULL_TREE);
	
	linemap_add(line_table, LC_ENTER, 0, filename, current_line);
	tree code_body = brainfuck_compile_scope(file, main_fndecl, ptr_decl, array_decl, true);
	append_to_statement_list(code_body, &stmt_list);

	tree current_bindexpr = build3_loc(current_location, BIND_EXPR, void_type_node, ptr_decl, stmt_list, current_block);
	DECL_INITIAL(main_fndecl) = current_block;
	DECL_SAVED_TREE(main_fndecl) = current_bindexpr;

	tree resdecl = build_decl(UNKNOWN_LOCATION, RESULT_DECL, NULL_TREE, integer_type_node);
	DECL_CONTEXT(resdecl) = main_fndecl;
	DECL_RESULT(main_fndecl) = resdecl;
	tree set_result = build2(INIT_EXPR, void_type_node, DECL_RESULT(main_fndecl), build_int_cst_type(integer_type_node, 0));
	tree return_stmt = build1(RETURN_EXPR, void_type_node, set_result);
	append_to_statement_list(return_stmt, &stmt_list);
	DECL_EXTERNAL(main_fndecl) = 0;
	DECL_PRESERVE_P(main_fndecl) = 1;
	
	gimplify_function_tree(main_fndecl);
	cgraph_node::finalize_function(main_fndecl, true);
	fclose(file);
}

void brainfuck_langhooks_parse_file(){
	
	if(num_in_fnames < 1){
		fatal_error(UNKNOWN_LOCATION, "no input files");	
	}
	if(num_in_fnames > 1){
		fatal_error(UNKNOWN_LOCATION, "Brainfuck can only compile on file at a time");
	}
	brainfuck_do_parse_file(in_fnames[0]);

	//brainfuck_do_fake_parse();
}

static tree brainfuck_langhooks_type_for_mode(enum machine_mode mode, int unsignedp){
	if (mode == TYPE_MODE(float_type_node))
		return float_type_node;
	
	if (mode == TYPE_MODE(double_type_node))
		return double_type_node;
	
	if (mode == TYPE_MODE(intQI_type_node))
		return unsignedp ? unsigned_intQI_type_node :intQI_type_node;
	if (mode == TYPE_MODE (intHI_type_node))
		return unsignedp ? unsigned_intHI_type_node : intHI_type_node;
	if (mode == TYPE_MODE (intSI_type_node))
		return unsignedp ? unsigned_intSI_type_node : intSI_type_node;
	if (mode == TYPE_MODE (intDI_type_node))
		return unsignedp ? unsigned_intDI_type_node : intDI_type_node;
	if (mode == TYPE_MODE (intTI_type_node))
		return unsignedp ? unsigned_intTI_type_node : intTI_type_node;
 
	if (mode == TYPE_MODE (integer_type_node))
		return unsignedp ? unsigned_type_node : integer_type_node;
 
	if (mode == TYPE_MODE (long_integer_type_node))
		return unsignedp ? long_unsigned_type_node : long_integer_type_node;
 
	if (mode == TYPE_MODE (long_long_integer_type_node))
		return unsignedp ? long_long_unsigned_type_node : long_long_integer_type_node;
 
 	if (COMPLEX_MODE_P (mode))
	{
		if (mode == TYPE_MODE (complex_float_type_node))
			return complex_float_type_node;
		if (mode == TYPE_MODE (complex_double_type_node))
			return complex_double_type_node;
		if (mode == TYPE_MODE (complex_long_double_type_node))
			return complex_long_double_type_node;
		if (mode == TYPE_MODE (complex_integer_type_node) && !unsignedp)
			return complex_integer_type_node;
    	}
	return NULL;
}

static tree brainfuck_langhooks_type_for_size(unsigned int bits, int unsignedp){
	//Unreachable
	gcc_unreachable();
	return NULL_TREE;
}

static tree brainfuck_langhooks_builtin_function (tree decl){
	return decl;
}

bool brainfuck_langhooks_global_bindings_p(){
	return false;
}

static tree brainfuck_langhooks_pushdecl(tree decl ATTRIBUTE_UNUSED){
	gcc_unreachable();
}

static tree brainfuck_langhooks_getdecls(){
	return NULL;
}

#undef LANG_HOOKS_NAME
#undef LANG_HOOKS_INIT
#undef LANG_HOOKS_PARSE_FILE
#undef LANG_HOOKS_TYPE_FOR_MODE
#undef LANG_HOOKS_TYPE_FOR_SIZE
#undef LANG_HOOKS_BUILTIN_FUNCTION
#undef LANG_HOOKS_GLOBAL_BINDINGS_P
#undef LANG_HOOKS_PUSHDECL
#undef LANG_HOOKS_GETDECLS

#define LANG_HOOKS_NAME			"GNU Brainfuck"
#define LANG_HOOKS_INIT			brainfuck_langhooks_init
#define LANG_HOOKS_PARSE_FILE		brainfuck_langhooks_parse_file
#define LANG_HOOKS_TYPE_FOR_MODE	brainfuck_langhooks_type_for_mode
#define LANG_HOOKS_TYPE_FOR_SIZE	brainfuck_langhooks_type_for_size
#define LANG_HOOKS_BUILTIN_FUNCTION	brainfuck_langhooks_builtin_function
#define LANG_HOOKS_GLOBAL_BINDINGS_P	brainfuck_langhooks_global_bindings_p
#define LANG_HOOKS_PUSHDECL		brainfuck_langhooks_pushdecl
#define LANG_HOOKS_GETDECLS		brainfuck_langhooks_getdecls


struct lang_hooks lang_hooks = LANG_HOOKS_INITIALIZER;

#include "gt-brainfuck-bf1.h"
#include "gtype-brainfuck.h"

