package Tokens is

   type Token_Type is (FEATURE_TOK, END_TOK, IF_TOK, PRINT_TOK, LOOP_TOK,
                       UNTIL_TOK, FROM_TOK, IS_TOK, ID_TOK, DO_TOK, ELSE_TOK,
                       THEN_TOK, ASSIGN_TOK, LIT_INT_TOK, ADD_TOK, SUB_TOK,
                       MUL_TOK, DIV_TOK, EQ_TOK, NE_TOK, LT_TOK, LE_TOK, GT_TOK,
                       GE_TOK, EOS_TOK, LEFT_PAREN_TOK, RIGHT_PAREN_TOK);

   type Token is private;

   LEXEME_SIZE: constant Positive := 10;

   type Lexeme is new String (1 .. LEXEME_SIZE);

   function create_token (tok_type: in Token_Type; lex: in Lexeme; row: in Positive;
                          col: in Positive) return Token;

   function get_token_type (tok: in Token) return Token_Type;

   function get_lexeme (tok: in Token) return Lexeme;

   function get_row_number (tok: in Token) return Positive;

   function get_column_number (tok: in Token) return Positive;

   function lexeme_length (lex: in Lexeme) return Positive;

   function to_lexeme (s: in String) return Lexeme;

private
   type Token is record
      tok_type: Token_Type;
      lex: Lexeme;
      row_number: Positive;
      column_number: Positive;
   end record;

end Tokens;
