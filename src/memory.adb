package body Memory is

   mem: array (Character range 'a' .. 'z') of Integer := (others => 0);
   -----------
   -- fetch --
   -----------

   function fetch (ch: in Character) return Integer is
   begin
      return mem (ch);
   end fetch;

   -----------
   -- store --
   -----------

   procedure store (ch: in Character; value: in Integer) is
   begin
      mem(ch) := value;
   end store;

end Memory;
