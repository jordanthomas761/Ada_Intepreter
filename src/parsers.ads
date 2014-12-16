with Lexical_Analyzers, Features, Statements;
use Lexical_Analyzers, Features, Statements;

package Parsers is

   parser_exception: exception;

   type Parser is private;

   function create_parser (file_name: in String) return Parser;

   procedure parse (p: in out Parser; f: out Feature);

private

   procedure get_Compound(lex: in out Lexical_Analyzer; comp: out Compound);

   type Parser is record
      lex: Lexical_Analyzer;
   end record;

end Parsers;
