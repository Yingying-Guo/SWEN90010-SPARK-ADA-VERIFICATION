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
      k : Natural := 0;  -- Tracks the number of bytes processed
   begin
      Output_Length := 0;
      Error := False;

      for I in Input'Range loop
         -- pragma Loop_Invariant(k < Output'Last);

         -- Check for current token's feasibility
         if (Input(I).offset > k) or else (k + Input(I).length > Output'Last) then
            Error := True;
            Output_Length := 0;
            return;
         end if;
      
         -- Byte-by-byte copying based on the current token
         for J in 0 .. Input(I).length - 1 loop
            if k - Input(I).offset + J + 1 <= 0 or else k + J + 1 > Output'Last then
               Error := True;
               Output_Length := 0;
               return;
            end if;
            Output(k + J + 1) := Output(k - Input(I).offset + J + 1);
         end loop;

         -- Adding the next byte while checking for bounds
         if k + Input(I).length + 1 > Output'Last then
            Error := True;
            Output_Length := 0;
            return;
         end if;

         Output(k + Input(I).length + 1) := Input(I).next_c;
         k := k + Input(I).length + 1;  -- Update k to reflect the new length
      end loop;

      Output_Length := k;  -- Set the output length after successful processing
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
