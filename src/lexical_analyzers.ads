with Tokens;
use Tokens;

private with Ada.Containers.Doubly_Linked_Lists;

package Lexical_Analyzers is

   lexical_exception: exception;

   type Lexical_Analyzer is private;

   function create_lexical_analyzer (file_name: in String) return Lexical_Analyzer;

   function more_tokens (lex: in Lexical_Analyzer) return Boolean;

   function get_lookahead_token (lex: in Lexical_Analyzer) return Token
     with pre => more_tokens (lex);

   procedure get_next_token (lex: in out Lexical_Analyzer; tok: out Token)
     with pre => more_tokens (lex);

private

   package Token_Lists is new Ada.Containers.Doubly_Linked_Lists (Token);

   type Lexical_Analyzer is record
      token_list: Token_Lists.List;
   end record;

end Lexical_Analyzers;
