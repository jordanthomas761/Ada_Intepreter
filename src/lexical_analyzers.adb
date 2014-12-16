with Ada.Text_IO, Ada.Characters.Handling, Ada.Characters.Latin_1;
use Ada.Text_IO, Ada.Characters.Handling, Ada.Characters.Latin_1;

package body Lexical_Analyzers is

   function is_all_digits (lex: in Lexeme) return Boolean is

      i: Positive := 1;

   begin
      while i <= lexeme_length (lex) and then is_digit (lex(i)) loop
         i := i + 1;
      end loop;
      return i > lexeme_length (lex);
   end is_all_digits;

   ---------------------------------------------------------------------------------------------------------------------------------

   function is_white_space (ch: in Character) return Boolean is

   begin
      return ch = space or ch = ht or ch = lf or ch = cr;
   end is_white_space;

   -------------------------------------------------------------------------

   procedure to_lower_case (lex: in out Lexeme) is

   begin
      lex := to_lexeme (to_lower (String (lex)));
   end to_lower_case;

   -------------------------------------------------------------------------

   procedure skip_white_space (line: in String; index: in out Positive) is

   begin
      while index <= line'length and then is_white_space (line(index)) loop
        index := index + 1;
      end loop;
   end skip_white_space;

   --------------------------------------------------------------------------

   function get_next_lexeme (line: in String; line_number: in Positive;
                             column_number: in Positive) return Lexeme is
      i: Positive := column_number;

   begin
      while i <= line'length and then not is_white_space (line(i)) loop
         i := i + 1;
      end loop;
      return to_lexeme (line (column_number .. i - 1));
   end get_next_lexeme;

   -------------------------------------------------------------------------

   function get_token_type (l: in Lexeme; line_number: in Positive;
                            column_number: in Positive) return Token_Type is

      tok_type: Token_Type;
   begin
      if is_letter (l(1)) then
         if lexeme_length (l) = 1 then
            tok_type := ID_TOK;
         elsif l = to_lexeme ("feature") then
            tok_type := FEATURE_TOK;
         elsif l = to_lexeme ("end") then
            tok_type := END_TOK;
         elsif l = to_lexeme ("if") then
            tok_type := IF_TOK;
         elsif l = to_lexeme ("print") then
            tok_type := PRINT_TOK;
         elsif l = to_lexeme ("loop") then
            tok_type := LOOP_TOK;
         elsif l = to_lexeme ("until") then
            tok_type := UNTIL_TOK;
         elsif l = to_lexeme ("from") then
            tok_type := FROM_TOK;
         elsif l = to_lexeme ("is") then
            tok_type := IS_TOK;
         elsif l = to_lexeme ("do") then
            tok_type := DO_TOK;
         elsif l = to_lexeme ("else") then
            tok_type := ELSE_TOK;
         elsif l = to_lexeme ("then") then
            tok_type := THEN_TOK;
         else
            raise lexical_exception with  "invalid identifier at row " &
              Positive'Image(line_number) & " and column " &
              Positive'Image (column_number);
         end if;
      elsif is_digit (l(1)) then
         if is_all_digits (l) then
            tok_type := LIT_INT_TOK;
         else
            raise lexical_exception with  "invalid integer constant at row " &
              Positive'Image(line_number) & " and column " &
              Positive'Image (column_number);
         end if;
      elsif l = to_lexeme (":=") then
         tok_type := ASSIGN_TOK;
      elsif l = to_lexeme ("+") then
         tok_type := ADD_TOK;
      elsif l = to_lexeme ("-") then
         tok_type := SUB_TOK;
      elsif l = to_lexeme ("*") then
         tok_type := MUL_TOK;
      elsif l = to_lexeme ("/") then
         tok_type := DIV_TOK;
      elsif l = to_lexeme ("=") then
         tok_type := EQ_TOK;
      elsif l = to_lexeme ("/=") then
         tok_type := NE_TOK;
      elsif l = to_lexeme ("<") then
         tok_type := LT_TOK;
      elsif l = to_lexeme ("<=") then
         tok_type := LE_TOK;
      elsif l = to_lexeme (">") then
         tok_type := GT_TOK;
      elsif l = to_lexeme (">=") then
         tok_type := GE_TOK;
      elsif l = to_lexeme ("(") then
         tok_type := LEFT_PAREN_TOK;
      elsif l = to_lexeme (")") then
         tok_type := RIGHT_PAREN_TOK;
      else
         raise lexical_exception with  "invalid lexeme at row " &
           Positive'Image(line_number) & " and column " &
           Positive'Image (column_number);
      end if;
      return tok_type;
   end get_token_type;

   ------------------------------------------------------------------------

   procedure process_line (lex: in out Lexical_Analyzer; line: in String;
                           line_number: in Positive) is

      index: Positive := 1;
      l: Lexeme;
      tok_type: Token_Type;

   begin
      skip_white_space (line, index);
      while index <= line'Length loop
         l := get_next_lexeme (line, line_number, index);
         to_lower_case (l);
         tok_type := get_token_type (l, line_number, index);
         Token_Lists.append (lex.token_list,
                             create_token (tok_type, l, line_number, index + 1));
         index := index + lexeme_length (l);
         skip_white_space (line, index);
      end loop;
   end process_line;

   -----------------------------
   -- create_lexical_analyzer --
   -----------------------------

   function create_lexical_analyzer (file_name: in String) return Lexical_Analyzer
   is
      lex: Lexical_Analyzer;
      line_number: Positive := 1;
      input: File_Type;
      size: Natural;
      line: String (1 .. 140);

   begin
      open (input, in_file, file_name);
      while not end_of_file (input) loop
         get_line (input, line, size);
         process_line (lex, line (1 .. size), line_number);
         line_number := line_number + 1;
      end loop;
      Token_Lists.append (lex.token_list,
                          create_token (EOS_TOK, to_lexeme ("EOS"), line_number, 1));
      close (input);
      return lex;
   end create_lexical_analyzer;

   -----------------
   -- more_tokens --
   -----------------

   function more_tokens (lex: in Lexical_Analyzer) return Boolean is
   begin
      return not Token_Lists.Is_Empty (lex.token_list);
   end more_tokens;

   -------------------------
   -- get_lookahead_token --
   -------------------------

   function get_lookahead_token (lex: in Lexical_Analyzer) return Token is
   begin
      return Token_Lists.First_Element (lex.token_list);
   end get_lookahead_token;

   --------------------
   -- get_next_token --
   --------------------

   procedure get_next_token (lex: in out Lexical_Analyzer; tok: out Token)is
   begin
      tok := Token_Lists.First_Element (lex.token_list);
      Token_Lists.Delete_First (lex.token_list);
   end get_next_token;

end Lexical_Analyzers;
