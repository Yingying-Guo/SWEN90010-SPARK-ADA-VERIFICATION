with LZ77; use LZ77;
with Ada.Text_IO;
with Ada.Integer_Text_IO;
use Ada.Text_IO;
use Ada.Integer_Text_IO;

procedure Main with
  SPARK_Mode
is
   -- a trivial token sequence that encodes the string "AAAB"
   --    T1    : Token_Array  (1..1):=
   --      (others => (Offset => 0, Length => 0, Next_C => 'A'));
   T1 : Token_Array (1 .. 2) :=
     (1 => (Offset => 0, Length => 0, Next_C => Character'Val (65)),
      2 => (Offset => 1, Length => 2, Next_C => Character'Val (66)));
--     T1    : Token_Array (1 .. 1)  := (2 => (Offset => 0, Length => 0, Next_C => Character'Val(0)));
   Error : Boolean;
   B     : Byte_Array (1 .. 100) :=
     (others => 'X');  -- Output_Array's buffer should in the range of (1..100)
   BLen  : Natural;
begin
--     for i in 0..0 loop
--        Put_Line("Loop works");
--        --- the loop would npot work if index range is 0..-1
--     end loop;

   -- T1: Input Array
   -- B: Output Array
   -- BLen: Output Array's length
   -- Error: Error flag
   Decode (T1, B, BLen, Error);
   if not Error then
      Put ("No error reported. Got this many bytes: ");
      Put (BLen);  -- print the length of the output array
      New_Line;
      -- If Output_Length <= Output_Array'Length, then the output array
      if BLen <= B'Length then
         for Index in B'First .. B'First + BLen - 1 loop
            Put (Item => B (Index)); -- print the output array
         end loop;
         New_Line;
      else
         Put ("Indicated decompressed length must be wrong!");
         New_Line;
      end if;
   end if;

   if Is_Valid (T1) then -- Check the validity of the input array
      Put("Valid and run the Deode_Fast");
      Decode_Fast (T1, B, BLen);
      Put ("Got this many: ");
      Put (BLen);
      New_Line;
      pragma Assert (BLen = 4);
      for Index in B'First .. B'First + BLen - 1 loop
         Put (Item => B (Index));
      end loop;
      New_Line;
   else
      Put ("Error reported.");
   end if;
end Main;
