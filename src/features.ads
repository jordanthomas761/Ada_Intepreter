with Statements;
use Statements;

package Features is

   type feature is private;

   function create_feature (com: in Compound) return Feature;

   procedure execute (f: in Feature);

private
   type feature is record
      com: Compound;
   end record;

end Features;
