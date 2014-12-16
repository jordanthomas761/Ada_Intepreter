with Lexical_Analyzers, Tokens, Features, Expressions, Boolean_Expressions, Statements;
use Lexical_Analyzers, Tokens, Features, Expressions, Boolean_Expressions, Statements;

package body Parsers is

   procedure match(tok: in Token; expected: Token_Type) is

   begin
      if get_token_type(tok) /= expected then
         raise parser_exception with " expected at row " & Positive'Image(get_row_number(tok)) &
           " and column " & Positive'Image(get_column_number(tok));
      end if;
   end match;

   procedure get_Arithmetic_Operator (lex: in out Lexical_Analyzer; op: out Arithmetic_Operator) is
      tok: Token;
   begin
      get_next_token(lex => lex, tok => tok);
      if get_token_type(tok => tok) = ADD_TOK then
         op := ADD_OP;
      elsif get_token_type(tok => tok) = SUB_TOK then
         op := SUB_OP;
      elsif get_token_type(tok => tok) = MUL_TOK then
         op := MUL_OP;
      elsif get_token_type(tok => tok) = DIV_TOK then
         op := DIV_OP;
      else
         raise parser_exception with "arithmetic operator expected at row " & Positive'Image(get_row_number(tok)) &
           " and column " & Positive'Image(get_column_number(tok));
      end if;
   end get_Arithmetic_Operator;

   procedure get_Relative_Operator (lex: in out Lexical_Analyzer; op: out Relational_Operator) is
      tok: Token;
   begin
      get_next_token(lex => lex, tok => tok);
      if get_token_type(tok => tok) = LT_TOK then
         op := LT_OP;
      elsif get_token_type(tok => tok) = LE_TOK then
         op := LE_OP;
      elsif get_token_type(tok => tok) = GT_TOK then
         op := GT_OP;
      elsif get_token_type(tok => tok) = GE_TOK then
         op := GE_OP;
      elsif get_token_type(tok => tok) = EQ_TOK then
         op := EQ_OP;
      elsif get_token_type(tok => tok) = NE_TOK then
         op := NE_OP;
      else
         raise parser_exception with "relational operator expected at row " & Positive'Image(get_row_number(tok)) &
           " and column " & Positive'Image(get_column_number(tok));
      end if;
   end get_Relative_Operator;

   procedure get_Expression(lex: in out Lexical_Analyzer; expr: out Expression_Access) is
      tok: Token;
      expr1: Expression_Access;
      expr2: Expression_Access;
      op: Arithmetic_Operator;

   begin
      tok:= get_lookahead_token(lex => lex);
      if get_token_type(tok => tok) = ID_TOK then
         get_next_token(lex => lex, tok => tok);
         expr := create_variable_expression(Character(get_lexeme(tok)(1)));
      elsif get_token_type(tok => tok) = LIT_INT_TOK then
         get_next_token(lex => lex, tok => tok);
         expr := create_constant_expression(Integer'Value(String(get_lexeme(tok))));
      else
         get_Arithmetic_Operator(lex => lex, op =>op);
         get_Expression(lex=> lex, expr => expr1);
         get_Expression(lex=> lex, expr => expr2);
         expr := create_binary_expression( op => op, expr1 =>expr1, expr2=> expr2);
      end if;
   end get_Expression;

   procedure get_Boolean_Expression (lex: in out Lexical_Analyzer; bool_expr: out Boolean_Expression) is
      op: Relational_Operator;
      expr1: Expression_Access;
      expr2: Expression_Access;
   begin
      get_Relative_Operator(lex => lex, op => op);
      get_Expression(lex => lex, expr => expr1);
      get_Expression(lex => lex, expr => expr2);
      bool_expr := create_boolean_expression(op => op, expr1 => expr1, expr2=> expr2);
   end get_Boolean_Expression;

   procedure get_If_Statement(lex: in out Lexical_Analyzer; s: out Statement_access) is
      tok: token;
      comp1: Compound;
      comp2: Compound;
      bool_expr: Boolean_Expression;
   begin
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => IF_TOK);
      get_Boolean_Expression(lex => lex, bool_expr => bool_expr);
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => THEN_TOK);
      get_Compound(lex=> lex, comp=> comp1);
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => ELSE_TOK);
      get_Compound(lex=> lex, comp=> comp2);
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => END_TOK);
      s:= create_if_statement(expr => bool_expr, com1 => comp1, com2 => comp2);

   end get_If_Statement;

   procedure get_Assignment_Statement(lex: in out Lexical_Analyzer; s: out Statement_access) is
      tok: token;
      ch: Character;
      expr: Expression_Access;
      var: Id;
   begin
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => ID_TOK);
      ch:= Character(get_lexeme(tok)(1));
      var:= create_id(ch => ch);
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => ASSIGN_TOK);
      get_Expression(lex => lex, expr => expr);
      s:= create_assignment_statement(var => var, expr => expr);
   end get_Assignment_Statement;

   procedure get_Loop_Statement(lex: in out Lexical_Analyzer; s: out Statement_access) is
      tok: token;
      expr: Boolean_Expression;
      comp: Compound;
      stmt: Statement_Access;
   begin
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => FROM_TOK);
      get_Assignment_Statement(lex => lex,s => stmt);
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => UNTIL_TOK);
      get_Boolean_Expression(lex => lex, bool_expr => expr);
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => LOOP_TOK);
      get_Compound(lex => lex, comp => comp);
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => END_TOK);      s := create_loop_statement(stmt => stmt,expr => expr,com => comp);
   end get_Loop_Statement;

   procedure get_Print_Statement(lex: in out Lexical_Analyzer; s: out Statement_access) is
      tok: token;
      expr: Expression_Access;
   begin
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => PRINT_TOK);
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => LEFT_PAREN_TOK);
      get_Expression(lex => lex, expr => expr);
      get_next_token(lex => lex, tok => tok);
      match(tok => tok, expected => RIGHT_PAREN_TOK);
      s := create_print_statement(expr => expr);
   end get_Print_Statement;

   procedure get_Statement(lex: in out Lexical_Analyzer; s: out Statement_access) is
      tok: token;
   begin
      tok:= get_lookahead_token(lex => lex);
      if get_token_type(tok => tok) = IF_TOK then
         get_If_Statement(lex => lex, s => s);
      elsif get_token_type(tok => tok) = ID_TOK then
         get_Assignment_Statement(lex => lex, s => s);
      elsif get_token_type(tok => tok) = FROM_TOK then
         get_Loop_Statement(lex => lex, s => s);
      elsif get_token_type(tok => tok) = PRINT_TOK then
         get_Print_Statement(lex => lex, s => s);
      else
         raise parser_exception with "statement expected at row " & Positive'Image(get_row_number(tok)) &
           " and column " & Positive'Image(get_column_number(tok));
      end if;

   end get_Statement;

   function is_valid_start_of_statement(tok: in Token) return boolean is
   begin
      return get_token_type(tok => tok) = ID_TOK or get_token_type(tok => tok) = FROM_TOK or
        get_token_type(tok => tok) = IF_TOK or get_token_type(tok => tok) = PRINT_TOK;
   end is_valid_start_of_statement;

   procedure get_Compound(lex: in out Lexical_Analyzer; comp: out Compound) is
      s: Statement_access;
      tok: Token;

   begin
      get_Statement(lex => lex, s => s);
      add(com=> comp,stmt => s);
      tok:= get_lookahead_token(lex => lex);
      while is_valid_start_of_statement(tok) loop
        get_Statement(lex => lex, s => s);
        add(com=> comp,stmt => s);
        tok:= get_lookahead_token(lex => lex);
      end loop;
   end get_Compound;

   function create_parser (file_name: in String) return Parser is

      par: Parser;

   begin
      par.lex := create_lexical_analyzer(file_name);
      return par;
   end create_parser;

   -----------
   -- parse --
   -----------

   procedure parse (p: in out Parser; f: out Feature) is
      id: lexeme;
      tok: Token;
      comp: Compound;

   begin
      get_next_token(lex => p.lex, tok => tok);
      match(tok => tok, expected => FEATURE_TOK);
      get_next_token(lex => p.lex, tok => tok);
      match(tok => tok, expected => ID_TOK);
      id:= get_lexeme(tok);
      get_next_token(lex => p.lex, tok => tok);
      match(tok => tok, expected => IS_TOK);
      get_next_token(lex => p.lex, tok => tok);
      match(tok => tok, expected => DO_TOK);
      get_Compound(lex => p.lex, comp=>comp);
      get_next_token(lex => p.lex, tok => tok);
      match(tok => tok, expected => END_TOK);

      f:= create_feature(com => comp);
   end parse;

end Parsers;
