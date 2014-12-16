with Memory, Ada.Text_IO;
use Memory, Ada.Text_IO;

package body Statements is

   ---------------------------------
   -- create_assignment_statement --
   ---------------------------------

   function create_assignment_statement (var: in Id; expr: in Expression_Access)
                                         return Statement_Access is
      stmt: Statement_Access;
   begin
      stmt := new Statement (ASSN_STMT);
      stmt.var := var;
      stmt.assn_expr := expr;
      return stmt;
   end create_assignment_statement;

   ---------------------------
   -- create_loop_statement --
   ---------------------------

   function create_loop_statement (stmt: in Statement_Access;  expr: Boolean_Expression;
                                   com: in Compound) return Statement_Access is

      s: Statement_Access;
   begin
      s := new Statement (LOOP_STMT);
      s.stmt := stmt;
      s.loop_expr := expr;
      s.com := com;
      return s;
   end create_loop_statement;

   -------------------------
   -- create_if_statement --
   -------------------------

   function create_if_statement (expr: in Boolean_Expression;
                                 com1, com2: in Compound)
                                 return Statement_Access is

      stmt: Statement_Access;
   begin
      stmt := new Statement (IF_STMT);
      stmt.expr := expr;
      stmt.com1 := com1;
      stmt.com2 := com2;
      return stmt;
   end create_if_statement;

   ----------------------------
   -- create_print_statement --
   ----------------------------

   function create_print_statement (expr: in Expression_Access)
                                    return Statement_Access is

      stmt: Statement_Access;

   begin
      stmt := new Statement (PRINT_STMT);
      stmt.pr_expr := expr;
      return stmt;
   end create_print_statement;

   -------------
   -- execute --
   -------------

   procedure execute (stmt: in Statement_Access) is

   begin
      case stmt.stmt_type is
         when ASSN_STMT =>
            store (get_ch (stmt.var), evaluate (stmt.assn_expr));
         when LOOP_STMT =>
            execute (stmt.stmt);
            while not evaluate (stmt.loop_expr) loop
               execute (stmt.com);
            end loop;
         when IF_STMT =>
            if evaluate (stmt.expr) then
               execute (stmt.com1);
            else
               execute (stmt.com2);
            end if;
         when PRINT_STMT =>
            put_line (Integer'Image (evaluate (stmt.pr_expr)));
      end case;
   end execute;

   ---------
   -- add --
   ---------

   procedure add (com: in out Compound; stmt: in Statement_Access) is

   begin
      Statement_Lists.Append (com.l, stmt);
   end add;

   -------------
   -- execute --
   -------------

   procedure execute (com: in Compound) is
      position: Statement_Lists.Cursor;

   begin
      position := Statement_Lists.first (com.l);
      for i in 1 .. Statement_Lists.Length (com.l) loop
         execute (Statement_Lists.element (position));
         Statement_Lists.next (position);
      end loop;
   end execute;


end Statements;
