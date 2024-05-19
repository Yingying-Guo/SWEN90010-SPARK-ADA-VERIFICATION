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

   -- 'Input' array: compressed token data
   -- 'Output' array: decompressed byte data.
   --  When successful,
   --     'Output_Length' indicates the length of the decompressed data
   --     'Error' should be set to False
   -- When an error occurs,
   --     'Output_Length' should be set to 0
   --     'Error' should be set to True

   -- Token (o, l, c):
   --     offset: Natural
   --     length: Natural
   --     next_c: Character
   --     the bytes bk+1,. . . , bk+1+(l−1) are identical to the bytes bk+1−o,. . . , bk+1−o+(l−1),
   --     byte bk+1+l is c
   procedure Decode
     (Input         : in     Token_Array; Output : in out Byte_Array;
      Output_Length :    out Natural; Error : out Boolean)
   is
      -- Tracks the number of bytes processed and Store the length of decompressed temperary output array
      -- Character'First represents ASCII NUL character
      k       : Integer := 0;  
   begin
      -- {True}
      Error         := False;
      
      -- Check for empty Input or empty Output(Output array's buffer range)
      if Input'Length > 0 and Input'Length <= Natural'Last
        and Output'Length > 0 and Output'Length <= Natural'Last 
      then
         -- Check for k that indicate the last element index of decompressed array and represent the length of the decompressed temperary output array
         -- At the begining, k should be 0
         -- The first token's offset should be 0
         if k = 0 
           and Input'First <= Input'Last and Input (Input'First).Offset = 0 then
            null;
         else 
            Error         := True;
            
         end if;
      else
         Error         := True;
  
      end if;
      
--        for I in Input'Range loop 
--           
--        end loop;
      
      if Error then
         -- {Error => k=0}
         k := 0;
         Output_Length := k;
         return;
         -- {Error => (k=0 and Output_Length=0)}
      else
         pragma Assert (not Error);
         pragma Assert (k = 0);
      -------------------------------------------------loop--------------------------------------------
         -- If Input is not empty, then the each token in Input Array must be valid
         for I in Input'Range loop
            -- Length_Acc(Input)(I) : Big_Integer
            pragma Loop_Invariant (k = 
                                   (if (Error or Input'Length <= 0) then 0 else 
                                    
                                          (if I = Input'First then To_Integer(Zero + To_Big_Integer (Input (I).Length) + To_Big_Integer (One))
                                           else (if I > Input'Last then To_Integer(Length_Acc (Input)(Input'Last)) 
                                                else To_Integer(Length_Acc (Input)(I - 1) + To_Big_Integer (Input (I).Length) + To_Big_Integer (One)
                                                 )
                                               )
                                             )
                                        )
                                     
                                  ); 
            
            if not Error and I >= Input'First and I <= Input'Last
              -- Check for after decompassing current token's length not causing the Integer overflow 
              and k >= 0 and k <= (Natural'Last - 1) 
              and Input (I).Length >= 0 and Input (I).Length <= (Natural'Last - 1)
            
              -- Check current token's offset not exceeding the maximum Integer length and curretn Decompressed array buffer(k)
              and Input (I).Offset >= 0 and Input (I).Offset <= Natural'Last and Input (I).Offset <= k
            then
               if k <= (Natural'Last - Input (I).Length) and k <= (Natural'Last - Input (I).Length - 1) then 
                  -- Check current output array length and Input (I).Length and after decompassing current token's length not exceeding the Output array buffer
                  if (k + Input (I).Length + 1) <= Output'Length then
                     null;
                  else
                     Error         := True;
                     k := 0;
                     Output_Length := k;
                     return;
                  end if;
               else
                  Error         := True;
                  k := 0;
                  Output_Length := k;
                  
                  return;
               end if;             
            else
--                 if Input (I).Length >= 0 then
--                    null;
--                 else
--                    Put("Error here");
--                 end if;
--                 New_Line;
--                 Put_Line("Error 2");
               Error         := True;
               k := 0;
               Output_Length := k;
               return;
            end if;

            -- Byte-by-byte copying based on the current token
            -- Token (o, l, c):
            --     the bytes bk+1,. . . , bk+1+(l−1) are identical to the bytes bk+1−o,. . . , bk+1−o+(l−1),
            --           the bytes bk+1,. . . , bk+l are identical to the bytes bk+1−o,. . . , bk+l−o,
            --     byte bk+1+l is c
            for J in 0 .. Input (I).Length - 1 loop
               pragma Loop_Invariant (if J < 0
                                      then (Output(Output'First - 1 + k) = Output(Output'First - 1 + k)) 
                                      else 
                                        (for all Q in 0..J-1 => 
                                           (Output (Output'First - 1 + k + 1 + Q) = Output (Output'First - 1 + k + 1 - Input (I).Offset + Q))
                                        )
                                     );
               Output (Output'First - 1 + k + 1 + J) := Output (Output'First - 1 + k + 1 - Input (I).Offset + J);
            end loop;

            if (k + Input (I).Length + 1) <= Natural'Last and (k + Input (I).Length + 1) <= Output'Length and not Error then
               Output (Output'First - 1 + k + Input (I).Length + 1) := Input (I).Next_C;
               k := k + Input (I).Length + 1;  -- Update k to reflect the new length
            else
               k := 0;
            end if;
            -- {{(Error => k = 0) and ((not Error) => k = (if (I >= Input'First and I <= Input'Last) then Length_Acc(Input)(I)) else Length_Acc(Input)(I)))}}
         end loop;
         -- {if Error then k = 0 else k = Length_Acc(Input)(I-1) and (I=Input'Last + 1))}
         -- {if Error then k = 0 else k = (if (I > Input'First and I <= Input'Last) then Length_Acc(Input)(I-1)) else Length_Acc(Input)(Input'Last)))}
         Output_Length := k;
         -- {k = (if Error then 0 else (if I > Input'Last then Length_Acc(Input)(Input'Last) else (Length_Acc(Input)(I) and (I = Input'Last)))) }
         -- {k = (if Error then 0 else Length_Acc(Input)(Input'Last))}
      end if;
      
      -- {if Error then Output_Length=0 else (Output_Length = Length_Acc(Input)(Input'Last) and Output_Length = k and k = Length_Acc(Input)(Input'Last))}
      -- {if Error then Output_Length=0 else (Length_Acc(Input)(Input'Last) = Length_Acc(Input)(Input'Last))}
      pragma Assert (if Error then Output_Length = 0 else True);
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
      Output_Length         := 0;
      
      Output (Output'First) := 'X'; -- for debugging
   end Decode_Fast;

end LZ77;
