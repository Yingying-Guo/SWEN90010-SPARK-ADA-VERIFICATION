with Ada.Text_IO; use Ada.Text_IO;
with Ada.Integer_Text_IO; use Ada.Integer_Text_IO;

-- Submission authored by:
-- <INSERT YOUR NAMES HERE>

-- This file requires Proof Level to be set to: <INSERT HERE>

package body LZ77 with SPARK_Mode is

   function Length_Acc(Input : in Token_Array) return Partial_Length is
      Result : Partial_Length (Input'Range) := (others => Zero);
   begin

      for Index in Input'Range loop
         -- Note this loop invariant needs "Proof level = 1" to prove it
         pragma Loop_Invariant
           ((for all I in Input'First .. Index-1 =>
              Result(I) =
            (if I = Input'First then Zero else Result(I - 1)) +
              To_Big_Integer(Input(I).Length) + To_Big_Integer(One)) and then
              (for all I in Input'First .. Index-1 =>
                    (for all J in Input'First..I-1 =>
               Result(I) > Result(J))));
         Result(Index) :=
           (if Index = Input'First then Zero else Result(Index - 1)) +
             To_Big_Integer(Input(Index).Length) + To_Big_Integer(One);
      end loop;
      return Result;
   end Length_Acc;

   procedure Put(T: in Token) is
   begin
      Put("Offset: "); Put(T.Offset); New_Line;
      Put("Length: "); Put(T.Length); New_Line;
      Put("Next_C: "); Put(T.Next_C); New_Line;
   end Put;

   procedure Decode(Input : in Token_Array; Output : in out Byte_Array;
                 Output_Length : out Natural; Error : out Boolean)
is
   Temp_Output_Length : Natural := 0;
begin
   Error := False;
   for I in Input'Range loop
      pragma Loop_Invariant
        (Temp_Output_Length <= Output'Last - Output'First and
         not Error);

      -- Check for out-of-bounds access on decoding:
      if Input(I).Offset > Temp_Output_Length then
         -- Error as required index does not exist in output
         Error := True;
         Output_Length := 0;
         return;  -- Exit on detection of error
      end if;

      -- Ensure there is enough space to append decoded data and Next_C
      if Output'Last < Output'First + Temp_Output_Length + Input(I).Length then
         Error := True;
         Output_Length := 0;
         return;  -- Exit if no space to append decoded data
      end if;

      -- Decode by copying data from Output based on Offset and Length
      for J in 1 .. Input(I).Length loop
         Output(Output'First + Temp_Output_Length + J) :=
            Output(Output'First + Temp_Output_Length - Input(I).Offset + J);
      end loop;
      Temp_Output_Length := Temp_Output_Length + Input(I).Length;

      -- Check space for Next_C
      if Output'Last < Output'First + Temp_Output_Length then
         Error := True;
         Output_Length := 0;
         return;  -- Exit if no space to append Next_C
      else
         Output(Output'First + Temp_Output_Length + 1) := Input(I).Next_C;
         Temp_Output_Length := Temp_Output_Length + 1;  -- Increment output length after appending
      end if;
   end loop;
   
   Output_Length := Temp_Output_Length;  -- Set final output length
   end Decode;
   
   function Is_Valid(Input : in Token_Array) return Boolean is
   begin
      -- IMPLEMENT THIS      
      return False;
   end Is_Valid;
   
   procedure Decode_Fast(Input : in Token_Array; Output : in out Byte_Array;
                         Output_Length : out Natural)
   is
   begin
      -- IMPLEMENT THIS            
      Output_Length := 0;
   end Decode_Fast;

end LZ77;
