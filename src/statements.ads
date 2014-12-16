with Expressions, Boolean_Expressions;
use Expressions, Boolean_Expressions;

private with Ada.Containers.Doubly_Linked_Lists;

package Statements is

   type Statement_Type is (ASSN_STMT, LOOP_STMT, IF_STMT, PRINT_STMT);

   type Statement (stmt_type: Statement_Type) is private;

   type Statement_Access is access Statement;

   type Compound is private;

   function create_assignment_statement (var: in Id; expr: in Expression_Access)
                                         return Statement_Access
     with pre => expr /= null;

   function create_loop_statement (stmt: in Statement_Access; expr: Boolean_Expression;
                                   com: in Compound) return Statement_Access
     with pre => stmt /= null;

   function create_if_statement (expr: in Boolean_Expression;
                                 com1, com2: in Compound) return Statement_Access;

   function create_print_statement (expr: in Expression_Access) return Statement_Access
     with pre => expr /= null;

   procedure execute (stmt: in Statement_Access)
     with pre => stmt /= null;

   procedure add (com: in out Compound; stmt: in Statement_Access)
     with pre => stmt /= null;

   procedure execute (com: in Compound);


private
   type Statement (stmt_type: Statement_Type) is record
      case stmt_type is
         when ASSN_STMT =>
            var: Id;
            assn_expr: Expression_Access;
         when LOOP_STMT =>
            stmt: Statement_Access;  -- need to look at
            loop_expr: Boolean_Expression;
            com: Compound;
         when IF_STMT =>
            expr: Boolean_Expression;
            com1: Compound;
            com2: Compound;
         when PRINT_STMT =>
            pr_expr: Expression_Access;
      end case;
   end record;

   package Statement_Lists is new Ada.Containers.Doubly_Linked_Lists (Statement_Access);

   type Compound is record
      l: Statement_Lists.List;
   end record;
end Statements;
