package body Tokens is

   ------------------
   -- create_token --
   ------------------

   function create_token (tok_type: in Token_Type; lex: in Lexeme;
                          row: in Positive; col: in Positive)
                          return Token is

      tok: Token;

   begin
      tok.tok_type := tok_type;
      tok.lex := lex;
      tok.row_number := row;
      tok.column_number := col;
      return tok;
   end create_token;

   --------------------
   -- get_token_type --
   --------------------

   function get_token_type (tok: in Token) return Token_Type is
   begin
      return tok.tok_type;
   end get_token_type;

   ----------------
   -- get_lexeme --
   ----------------

   function get_lexeme (tok: in Token) return Lexeme is
   begin
      return tok.lex;
   end get_lexeme;

   --------------------
   -- get_row_number --
   --------------------

   function get_row_number (tok: in Token) return Positive is
   begin
      return tok.row_number;
   end get_row_number;

   -----------------------
   -- get_column_number --
   -----------------------

   function get_column_number (tok: in Token) return Positive is
   begin
      return tok.column_number;
   end get_column_number;

   -------------------------------------------------------------------

   function lexeme_length (lex: in Lexeme) return Positive is

      i: Positive := LEXEME_SIZE;

   begin
      while lex(i) = ' ' loop
         i := i - 1;
      end loop;
      return i;
   end lexeme_length;

   ---------------------------------------------------------------------

   function to_lexeme (s: in String) return Lexeme is

      lex: Lexeme := (others => ' ');

   begin
      if s'length <= LEXEME_SIZE then
         for i in 1 .. s'length loop
            lex(i) := s(i + s'first - 1);
         end loop;
      else
         for i in 1 .. LEXEME_SIZE loop
            lex (i) := s(i + s'first - 1);
         end loop;
      end if;
      return lex;
   end to_lexeme;

end Tokens;
