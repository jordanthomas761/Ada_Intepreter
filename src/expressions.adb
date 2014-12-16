with Memory;
use Memory;

package body Expressions is

   function create_id (ch: in Character) return Id is

      var: Id;
   begin
      var.ch := ch;
      return var;
   end create_id;

   -------------------------------------------------------------------------------------------------------------------------------

   function evaluate (var: in Id) return Integer is

   begin
      return fetch (var.ch);
   end evaluate;

   --------------------------------
   -- create_constant_expression --
   --------------------------------

   function create_constant_expression (value: in Integer) return Expression_Access is
      expr: Expression_Access;
   begin
      expr := new Expression (CONST_EXPR);
      expr.value := value;
      return expr;
   end create_constant_expression;

   --------------------------------
   -- create_variable_expression --
   --------------------------------

   function create_variable_expression (ch: in Character) return Expression_Access is

      expr: Expression_Access;

   begin
      expr := new Expression (VAR_EXPR);
      expr.var := create_id (ch);
      return expr;
   end create_variable_expression;

   ------------------------------
   -- create_binary_expression --
   ------------------------------

   function create_binary_expression (op: in Arithmetic_Operator;
                                      expr1, expr2: in Expression_Access)
                                      return Expression_Access is
      expr: Expression_Access;

   begin
      expr := new Expression (BINARY_EXPR);
      expr.op := op;
      expr.expr1 := expr1;
      expr.expr2 := expr2;
      return expr;
   end create_binary_expression;

   --------------
   -- evaluate --
   --------------

   function evaluate (expr: in Expression_Access) return Integer is
      result: Integer;

   begin
      case expr.expr_type is
         when BINARY_EXPR =>
            case expr.op is
               when ADD_OP =>
                  result := evaluate(expr.expr1) + evaluate (expr.expr2);
               when SUB_OP =>
                  result := evaluate(expr.expr1) - evaluate (expr.expr2);
               when MUL_OP =>
                  result := evaluate(expr.expr1) * evaluate (expr.expr2);
               when DIV_OP =>
                  result := evaluate(expr.expr1) / evaluate (expr.expr2);
            end case;
         when CONST_EXPR =>
            result := expr.value;
         when VAR_EXPR =>
            result := evaluate (expr.var);
      end case;
      return result;
   end evaluate;

   -----------------------------------------------------------------------------------------------------------------------------

   function get_ch (var: in Id) return Character is

   begin
      return var.ch;
   end get_ch;

end Expressions;
