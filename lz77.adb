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
   procedure Decode
     (Input         : in     Token_Array; Output : in out Byte_Array;
      Output_Length :    out Natural; Error : out Boolean)
   is
      -- Tracks the number of bytes processed and Store the length of decompressed temperary output array
      -- Character'First represents ASCII NUL character
      k       : Natural := 0;  
      One_c: constant Natural := 1;
      J : Natural := 0;
      I : Natural;
   begin
      -- {True}
      Error         := False;
      -- {Not Error and True}   
      -- Check for empty Input or empty Output (Output array's buffer range) and Check their indexes not cause overflow
      -- {(if Error then True else True)=>(True)}
      if not (Input'Length > 0 and Input'Length <= (Natural'Last - 1)
         and Input'Last <= (Natural'Last - 1) and Input'First <= Natural'Last
         and Output'Length > 0 and Output'Length <= Natural'Last
         and Input'Length <= Output'Length  
         and Output'Last <= Natural'Last and Output'First <= Natural'Last) then
         -- {Error} and {if Error then True else True}
         -- {Error} and {if Error then 0=0 else True}
         k := 0;
         -- {Error} and {if Error then k=0 else True}
         Output_Length := k;
         Error := True;
         return;
         -- {Error} and {if Error then Output_Length=0 else True}
      else
         I := Input'First;
      -- If Input is not empty, then the each token in Input Array must be valid
         while I >= Input'First and I <= Input'Last loop
            -- Length_Acc(Input)(I) : Big_Integer
            pragma Loop_Invariant ((if Error then k=0 else True) and I >= Input'First and I <= Input'Last and Input'Last <= Natural'Last - 1);
            
            if Error 
              or not (
                 k <= (Output'Length - Input(I).Length - 1)
                 and not (Input(I).Offset > 0 and Input(I).Length = 0)
                 and Input(I).Offset <= k
                 and Output'First <= (Natural'Last - Input(I).Length - k - 1)
                 and Output'Last <= Natural'Last
                 and Input(I).Length <= Output'Length) 
            then 
               k := 0;
               Output_Length := k;
               Error := True;
               -- {Error and (if Error then Output_Length=0 else True)}
               return;
            else
                  --  Byte-by-byte copying based on the current token
                  --  Token (o, l, c):
                  --  the bytes bk+1,. . . , bk+1+(l−1) are identical to the bytes bk+1−o,. . . , bk+1−o+(l−1),
                  --  the bytes bk+1,. . . , bk+l are identical to the bytes bk+1−o,. . . , bk+l−o,
                  --  byte bk+1+l is c
                  while J >= 0 and J <= Input (I).Length - 1 loop
--                       pragma Loop_Invariant (not Error and J >= 0 and J <= Input(I)'Length and k <= (Output'Length - Input(I).Length - 1) and  and (for ));
                     -- Only here in the loop where Error = False
                     Output (Output'First + k + J) := Output (Output'First + k - Input (I).Offset + J);
                     J := J+1;
                  end loop;
                  -- here in the loop should be Error = False
                  Output (Output'First + k + Input (I).Length) := Input (I).Next_C;
                  k := k + Input (I).Length + 1;
                  -- {not Error and J = Input(I).Length and (if Error then k=0 else True)}
            end if;
            I := I + 1; -- I >= Input'First
            -- {if Error then k=0 else True}
         end loop;
         -- {not Error and I = (Input'Last + 1) and (if Error then k=0 else "True")}
         -- {not Error and (if Error then k=0 else True)}
         Output_Length := k; 
         -- {not Error and (if Error then Output_Length=0 else True)}
      end if;
      -- {if Error then Output_Length=0 else True}
   end Decode;


   --  function Valid(Input : in Token_Array; Upto : in Integer) return Boolean is
   --    (
   --     Upto <= Input'Last and then
   --     (Input'Length = 0 or else
   --       (for all I in Input'First .. Upto =>
   --             In_Range(Arg => Length_Acc(Input)(I),
   --                      Low => To_Big_Integer(One),
   --                      High => To_Big_Integer(Integer'Last)) and
   --          To_Big_Integer(Input(I).Offset) <=
   --        (if I = Input'First then Zero else Length_Acc(Input)(I-1)) and
   --        (if Input(I).Offset = 0 then Input(I).Length = 0)
   --       )
   --    ));

   -- 'Input' array: compressed data
   -- return True or False
   -- Post => (Valid(Input, Input'Last));
   function Is_Valid (Input : in Token_Array) return Boolean is
      k : Natural;
      Last_Length : Natural;
      I : Natural;
   begin
      if Input'Length = 0 
      then return True;
      else 
         if not (Input'Length <= (Natural'Last - 1)
                 and Input'Last <= (Natural'Last - 1) and Input'First <= Natural'Last) 
         then
            return False;
         else
            k := 1;
            Last_Length := 0;
            I := Input'First;
            -- If Input is not empty, then the each token in Input Array must be valid
            While I >= Input'First and I <= Input'Last loop
               pragma Loop_Invariant
                 (if Input'Length > 0 then 
                    (I >= Input'First 
                     and I <= Input'Last + 1 
                     and k >= 1 
                     and (if (I <= Input'Last 
                       and Last_Length <= (Natural'Last - Input(I).Length - 1)
                       and (if I = Input'First then Last_Length = 0)
                       and Input(I).Offset <= Last_Length
                       and (if Input(I).Offset = 0 then Input(I).Length = 0)) 
                     then k = Last_Length + Input (I).Length + 1) 
                    )
                else True);
               if I = Input'First then Last_Length:= 0; 
               else Last_Length := k;
               end if;
               --  pragma Loop_Invariant ((if Error then k=0 else True) and I >= Input'First and I <= Input'Last and Input'Last <= Natural'Last - 1);    
               if not (if Input(I).Offset = 0 then Input(I).Length = 0)
                 or not (Input(I).Offset <= Last_Length and Last_Length <= (Natural'Last - Input(I).Length - 1)) 
               then 
                  return False;
               else 
                  k := Last_Length + Input (I).Length + 1;
                  if not (Last_Length < k and k >= 1) 
                  then return False; 
                  end if;
               end if;
               I := I + 1; 
               -- I >= Input'First
            end loop;
         end if;
      end if;
      return True;
   end Is_Valid;
   
   
--     Pre => Valid(Input,Input'Last) and then Output'Length >= To_Integer(Decoded_Length(Input)),
--     Post => Output_Length = To_Integer(Decoded_Length(Input));
   procedure Decode_Fast
     (Input         : in     Token_Array; Output : in out Byte_Array;
      Output_Length :    out Natural)
   is
      k : Natural := 0;
   begin
      if Input'Length = 0 then 
         Output_Length := k;
      else
         for I in Input'First..Input'Last loop
            for J in 0 .. Input (I).Length - 1 loop
--          pragma Loop_Invariant (not Error and J >= 0 and J <= Input(I)'Length and k <= (Output'Length - Input(I).Length - 1) and  and (for ));
--          Only here in the loop where Error = False
               Output (Output'First + k + J) := Output (Output'First + k - Input (I).Offset + J);
            end loop;
            -- here in the loop should be Error = False
            Output (Output'First + k + Input (I).Length) := Input (I).Next_C;
            k := k + Input (I).Length + 1;
         end loop;
         Output_Length := k;
      end if;
   end Decode_Fast;

end LZ77;
