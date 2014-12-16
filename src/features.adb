package body Features is

   --------------------
   -- create_feature --
   --------------------

   function create_feature (com: in Compound) return Feature is

      f: feature;

   begin
      f.com := com;
      return f;
   end create_feature;

   -------------
   -- execute --
   -------------

   procedure execute (f: in Feature) is
   begin
      execute (f.com);
   end execute;

end Features;
