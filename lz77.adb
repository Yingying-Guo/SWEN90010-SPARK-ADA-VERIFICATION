with Ada.Text_IO;         use Ada.Text_IO;
with Ada.Integer_Text_IO; use Ada.Integer_Text_IO;

-- Submission authored by:
-- Yingying Guo, Wenwen Yan

-- This file requires Proof Level to be set to: <at least 1>

package body LZ77 with
  SPARK_Mode
is

   function Length_Acc (Input : in Token_Array) return Partial_Length is
      Result : Partial_Length (Input'Range) := (others => Zero);
   begin

      for Index in Input'Range loop
         -- Note this loop invariant needs "Proof level = 1" to prove it
         pragma Loop_Invariant
           ((for all I in Input'First .. Index - 1 =>
               Result (I) =
               (if I = Input'First then Zero else Result (I - 1)) +
                 To_Big_Integer (Input (I).Length) + To_Big_Integer (One))
            and then
            (for all I in Input'First .. Index - 1 =>
               (for all J in Input'First .. I - 1 =>
                  Result (I) > Result (J))));
         Result (Index) :=
           (if Index = Input'First then Zero else Result (Index - 1)) +
           To_Big_Integer (Input (Index).Length) + To_Big_Integer (One);
      end loop;
      return Result;
   end Length_Acc;

   procedure Put (T : in Token) is
   begin
      Put ("Offset: ");
      Put (T.Offset);
      New_Line;
      Put ("Length: ");
      Put (T.Length);
      New_Line;
      Put ("Next_C: ");
      Put (T.Next_C);
      New_Line;
   end Put;

   -- 'Input' array: compressed data
   -- 'Output' array: uncompressed data.
   --  When successful,
   --     'Output_Length' indicates the length of the decompressed data
   --     'Error' should be set to False
   -- When an error occurs,
   --     'Output_Length' should be set to 0
   --     'Error' should be set to True

   -- Token (o, l, c):
   --     the bytes bk+1,. . . , bk+1+(l−1) are identical to the bytes bk+1−o,. . . , bk+1−o+(l−1),
   --     byte bk+1+l is c
   procedure Decode
     (Input         : in     Token_Array; Output : in out Byte_Array;
      Output_Length :    out Natural; Error : out Boolean)
   is
      largest : Integer := Integer'Last;
      one     : Integer := 1;
      k       : Natural := 0;  -- Tracks the number of bytes processed
   begin
      Output_Length := 0;
      Error         := False;

      -- Check for empty input
      if Input'Length <= 0 then
         Output_Length := 0;
         Error         := True;
         return;
      end if;
      -- check overflow

      -- Check for k that indicate the output array index
      k := Input (Input'First).Offset;
      if k < 0 then
         Output_Length := 0;
         Error         := True;
         return;
      end if;
      -- check overflow

      -- If Input is not empty, then the each token in Input Array must be valid
      for I in Input'Range loop
         -- pragma Loop_Invariant (if Error = False then Temp_Output_Length = Length_Acc(Input)(I) else Output_Length = 0);

         -- Check for current token's feasibility
         if (Input (I).Offset >= k) and k >= 0 then
            Error         := True;
            Output_Length := 0;
            return;
         end if;

         if (k + Input (I).Length > Output'Last) then
            Error         := True;
            Output_Length := 0;
            return;
         end if;

         -- Byte-by-byte copying based on the current token
         for J in 0 .. Input (I).Length - 1 loop
            if k - Input (I).Offset + J + 1 <= 0
              or else k + J + 1 > Output'Last
            then
               Error         := True;
               Output_Length := 0;
               return;
            end if;
            Output (k + J + 1) := Output (k - Input (I).Offset + J + 1);
         end loop;

         -- Adding the next byte while checking for bounds
         if k + Input (I).Length + 1 > Output'Last then
            Error         := True;
            Output_Length := 0;
            return;
         end if;

         Output (k + Input (I).Length + 1) := Input (I).Next_C;
         k := k + Input (I).Length + 1;  -- Update k to reflect the new length
      end loop;

      Output_Length := k;  -- Set the output length after successful processing
   end Decode;

   -- 'Input' array: compressed data
   --  return： True or False
   function Is_Valid (Input : in Token_Array) return Boolean is
   begin
      -- IMPLEMENT THIS
      return False;
   end Is_Valid;

   procedure Decode_Fast
     (Input         : in     Token_Array; Output : in out Byte_Array;
      Output_Length :    out Natural)
   is
   begin
      -- IMPLEMENT THIS
      Output_Length := 0;
   end Decode_Fast;

end LZ77;
