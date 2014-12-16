package Expressions is

   type Arithmetic_Operator is (ADD_OP, SUB_OP, MUL_OP, DIV_OP);

   type Expression_Type is (BINARY_EXPR, CONST_EXPR, VAR_EXPR);

   type Expression (expr_type: Expression_Type) is private;

   type Expression_Access is access Expression;

   type Id is private;

   function create_id (ch: in Character) return Id;

   function create_constant_expression (value: in Integer) return Expression_Access;

   function create_variable_expression (ch: in Character) return Expression_Access;

   function create_binary_expression (op: in Arithmetic_Operator;
                                      expr1, expr2: in Expression_Access)
                                      return Expression_Access
     with pre => expr1 /= null and expr2 /= null;

   function evaluate (expr: in Expression_Access) return Integer
     with pre => expr /= null;

   function evaluate (var: in id) return Integer;

   function get_ch (var: in Id) return Character;

private
   type Expression (expr_type: Expression_Type) is
      record
         case expr_type is
            when CONST_EXPR =>
               value: Integer;
            when VAR_EXPR =>
               var: Id;
            when BINARY_EXPR =>
               op: Arithmetic_Operator;
               expr1: Expression_Access;
               expr2: Expression_Access;
         end case;
      end record;

   type Id is record
      ch: Character;
   end record;

end Expressions;
