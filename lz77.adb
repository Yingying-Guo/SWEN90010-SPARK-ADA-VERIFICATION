with Ada.Text_IO;         use Ada.Text_IO;
with Ada.Integer_Text_IO; use Ada.Integer_Text_IO;

-- Submission authored by:
-- Yingying Guo, Wenwen Yan

-- This file requires Proof Level to be set to: 1

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

   -- 'Input' array: compressed token data
   -- 'Output' array: decompressed byte data.
   --  When successful,
   --     'Output_Length' indicates the length of the decompressed data
   --     'Error' should be set to False
   -- When an error occurs,
   --     'Output_Length' should be set to 0
   --     'Error' should be set to True
   procedure Decode
     (Input         : in     Token_Array; Output : in out Byte_Array;
      Output_Length :    out Natural; Error : out Boolean)
   is
      -- Index of the main loop
      I           : Natural;
      -- Index of the nested loop
      J           : Natural;
      -- Store the length of last decompressed temporary output array
      Last_Length : Natural;
      -- Tracks the number of bytes processed and Store the length of decompressed temporary output array
      k           : Natural := 0;
   begin
      Error := False;
      -- Check for empty Input and when accessing the Input array, the index would not go out of bounds or cause integer overflow
      if not
        (Input'Length > 0   
         and Input'Last <= (Natural'Last - 1) and Input'First <= Natural'Last
         -- Check for empty Output and when accessing the Output array, the index would not go out of bounds or cause integer overflow
         and Output'Length > 0 and Output'Length <= (Natural'Last - 1) 
         and Output'Last <= (Natural'Last - 1) and Output'First <= Natural'Last
         -- Check that decompressing Input and storing it in Output (Output array's buffer range) would not cause buffer overflow
         and Input'Length <= Output'Length)
      then
         k             := 0;
         Output_Length := k;
         Error         := True;
         return;
      else
         -- Initialize I to the first index of Input and Last_Length to 0
         I           := Input'First;
         Last_Length := 0;
         -- If Input is not empty, then each token in the Input Array must be valid
         while I >= Input'First and I <= Input'Last loop
            -- Loop Invariant to ensure the correctness of the main loop
            pragma Loop_Invariant
              (if Error then k = 0 else
                  (if I > Input'First then
                      (Output(Output'First + Last_Length + Input (I - 1).Length) = Input (I - 1).Next_C 
                       and k = Last_Length + Input (I - 1).Length + 1)));
            I := I + 1;

            if Error or
              -- Check for the current position k is within the range of the Output array after considering the length of the current token in the Input array
               -- and also the calculation not cause Integer overflow
               not
               (k <= (Output'Length - Input (I - 1).Length - 1)
               and Output'First <= (Natural'Last - Input (I - 1).Length - k) 
               -- Check for the offset of the token is valid
               and (if Input (I - 1).Offset = 0 then Input (I - 1).Length = 0) 
               and Input (I - 1).Offset <= k 
               )
            then
               -- If any of the above conditions are not met, set k to 0, Output_Length to k and Error to True, then return
               k             := 0;
               Output_Length := k;
               Error         := True;
               return;
            else
               -- Initialize J to 0
               J := 0;

               -- Byte-by-byte copying based on the current token
               -- Token (o, l, c):
               -- the bytes bk+1,. . . , bk+1+(l-1) are identical to the bytes bk+1-o,. . . , bk+1+(l-1)-o,
               -- the bytes bk+1,. . . , bk+l       are identical to the bytes bk+1  ,. . . , bk+l-o,
               -- byte bk+1+l is c
               while J >= 0 and J <= Input (I - 1).Length - 1 loop
                  -- Loop Invariant to ensure the correctness of the nested loop
                  pragma Loop_Invariant
                    (if J > 0 then
                        Output (Output'First + k + J - 1) = Output(Output'First + k - Input (I - 1).Offset + J - 1));
                  -- Copy the byte from the offset position to the current position
                  Output (Output'First + k + J) := Output (Output'First + k - Input (I - 1).Offset + J);
                  J := J + 1;
               end loop;
               -- Set the next byte to the next character in the Input
               Output (Output'First + k + Input (I - 1).Length) := Input (I - 1).Next_C;
               -- Update Last_Length and k
               Last_Length := k;
               k := Last_Length + Input (I - 1).Length + 1;
            end if;
         end loop;
         -- when there is not error set Output_Length to k, where k indicates the length of the decompressed data
         Output_Length := k;
      end if;
   end Decode;

   function Is_Valid (Input : in Token_Array) return Boolean is
      k           : Natural;
      Last_Length : Natural;
--        I           : Natural;
      Flag        : Boolean := True;
   begin
      if Input'Length = 0 then return Flag; end if;

      if Input'Length < 0 then Flag := False; return Flag; end if;

--        if Input'Length > (Natural'Last - 1) then Flag := False; return Flag; end if;
      
--        if Input'Last > (Natural'Last - 1) then Flag := False; return Flag; end if;

--        if Input'First > Natural'Last then Flag := False; return Flag; end if;
      
      k := 0;
--        I := Input'First;

      -- If Input is not empty, then the each token in Input Array must be valid
      for I in Input'First ..  Input'Last loop

         
         Last_Length := k;
--           exit when I > Input'Last;
         
         if Natural'Last - Input(I).Length - 1 < Last_Length then Flag := False; return Flag; 
         end if;
            
         k := Last_Length + Input(I).Length + 1;
            
         if k < 1 or k <= Last_Length then Flag := False; return Flag; end if;
         
         if Input (I).Offset = 0 and Input (I).Length /= 0 then Flag := False; return Flag; end if;
         
         if Input (I).Offset > Last_Length then Flag := False; return Flag; end if;
         
--           I := I + 1;
         pragma Loop_Invariant(k <= Natural'Last);
         pragma Loop_Invariant
            (Input'Length > 0 and
            Input'Last <= Natural'Last and
            Input'First <= Natural'Last);
         pragma Loop_Invariant (I >= Input'First); 
         
         pragma Loop_Invariant
            (k >= 1 and k <= Integer'Last and
            (if I > Input'First then
               (if (Last_Length <= (Natural'Last - Input (I).Length - 1) and (if I = Input'First then Last_Length = 0))
                  then k = Last_Length + Input (I).Length + 1)));
         
         pragma Loop_Invariant ( k = (if I = Input'First then 1 else To_Integer(Length_Acc(Input)(I)))  
                                 and Valid(Input, I));
         
      end loop;
      return Flag;
   end Is_Valid;

   --     Pre => Valid(Input,Input'Last) and then Output'Length >= To_Integer(Decoded_Length(Input)),
   --     Post => Output_Length = To_Integer(Decoded_Length(Input));
   procedure Decode_Fast
     (Input         : in     Token_Array; Output : in out Byte_Array;
      Output_Length :    out Natural)
   is
      k : Natural := 0;
      I : Natural;
      J : Natural;
      --        Last_Length : Natural;
   begin
      if Input'Length <= 0 then
         k             := 0;
         Output_Length := k;
      else
         I := Input'First;
         while I >= Input'First and I <= Input'Last loop         
            J := 0;
            while J >= 0 and J <= Input (I).Length - 1 loop
               --                 pragma Loop_Invariant (J >= 0 and J <= Input(I - 1).Length and Output'First <= Natural'Last - k - J and To_Big_Integer(Input(I - 1).Offset) <= Length_Acc(Input)(I - 1));
               Output (Output'First + k + J) :=  Output (Output'First + k - Input (I).Offset + J);
               J := J + 1;
            end loop;
            Output (Output'First + k + Input (I).Length) := Input (I).Next_C;
            k := k + Input (I).Length + 1;
            I := I + 1;
         end loop;
         Output_Length := k;
      end if;
   end Decode_Fast;

end LZ77;
