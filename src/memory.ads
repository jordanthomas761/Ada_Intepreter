package Memory is

   function fetch (ch: in Character) return Integer
     with pre => ch >= 'a' and ch <= 'z';

   procedure store (ch: in Character; value: in Integer)
     with pre => ch >= 'a' and ch <= 'z';

end Memory;
