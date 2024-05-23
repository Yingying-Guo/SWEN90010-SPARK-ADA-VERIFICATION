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
      --- Last_Length 
      I : Natural;
      Last_Length : Natural;
      J : Natural;
   begin
      -- {True}
      Error         := False;
      -- {Not Error and True}   
      -- Check for empty Input or empty Output (Output array's buffer range) and Check their indexes not cause overflow
      -- {(if Error then True else True)=>(True)}
      if not (Input'Length > 0 and Input'Length <= (Natural'Last - 1)
         and Input'Last <= (Natural'Last - 1) and Input'First <= Natural'Last
         and Output'Length > 0 and Output'Length <= (Natural'Last - 1)  
         and Output'Last <= (Natural'Last - 1) and Output'First <= Natural'Last
         and Input'Length <= Output'Length
      ) then
         -- {Error} and {if Error then 0=0 else True}
         k := 0;
         Output_Length := k;
         Error := True;
         return;
         -- {Error} and {if Error then Output_Length=0 else True}
      else
         I := Input'First;
         Last_Length := 0;
      -- If Input is not empty, then the each token in Input Array must be valid
         while I >= Input'First and I <= Input'Last loop
            pragma Loop_Invariant (
               I >= Input'First and I <= Input'Last + 1
               and Input'Length > 0 and Input'Length <= (Natural'Last - 1)
               and Input'Last <= (Natural'Last - 1) and Input'First <= Natural'Last
               and Output'Length > 0 and Output'Length <= (Natural'Last - 1)  
               and Output'Last <= (Natural'Last - 1) and Output'First <= Natural'Last
               and Input'Length <= Output'Length
               and (if Error then k=0 else 
                      (if I > Input'First then (Output (Output'First + Last_Length + Input (I - 1).Length) = Input (I - 1).Next_C and k = Last_Length + Input (I - 1).Length + 1))));
            I := I + 1;
            if Error 
              or not (
                 k <= (Output'Length - Input(I - 1).Length - 1)
                 and (if Input(I - 1).Offset = 0 then Input(I - 1).Length = 0)
                 and Input(I - 1).Offset <= k
                 and Output'First <= (Natural'Last - Input(I - 1).Length - k)) 
            then 
               k := 0;
               Output_Length := k;
               Error := True;          
               return;
            else
               J := 0;
               --  Byte-by-byte copying based on the current token
               --  Token (o, l, c):
               --  the bytes bk+1,. . . , bk+1+(l-1) are identical to the bytes bk+1-o,. . . , bk+1+(l-1)-o,
               --  the bytes bk+1,. . . , bk+l       are identical to the bytes bk+1  ,. . . , bk+l−o,
               --  byte bk+1+l is c
               while J >= 0 and J <= Input (I - 1).Length - 1 loop
                  pragma Loop_Invariant 
                  (Input'Length > 0 and Input'Length <= (Natural'Last - 1)
                     and Input'Last <= (Natural'Last - 1) and Input'First <= Natural'Last
                     and Output'Length > 0 and Output'Length <= (Natural'Last - 1)  
                     and Output'Last <= (Natural'Last - 1) and Output'First <= Natural'Last
                     and Input'Length <= Output'Length
                     -----------------------------------
                     and not Error 
                     and k <= (Output'Length - Input(I - 1).Length - 1)
                     and (if Input(I - 1).Offset = 0 then Input(I - 1).Length = 0)
                     and Input(I - 1).Offset <= k
                     and Output'First <= (Natural'Last - Input(I - 1).Length - k)
                     -----------------------------------------
                     and J >= 0 and J <= Input(I - 1).Length 
                     and (if J > 0
                     then Output (Output'First + k + J - 1) = Output (Output'First + k - Input (I - 1).Offset + J - 1)));
                  Output (Output'First + k + J) := Output (Output'First + k - Input (I - 1).Offset + J);
                  J := J + 1;
               end loop;
               -- here in the loop should be Error = False
               Output (Output'First + k + Input (I - 1).Length) := Input (I - 1).Next_C;
               Last_Length := k;
               k := Last_Length + Input (I - 1).Length + 1;
               -- {not Error and J = Input(I).Length and (if Error then k=0 else True)}
            end if;
            -- {if Error then k=0 else True}
         end loop;
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
   function Is_Valid (Input : in Token_Array) return Boolean is
      k : Natural;
      Last_Length : Natural;
      I : Natural;
      Flag : Boolean := True;
   begin
      if Input'Length > 0 
      then 
         if not (Input'Length <= (Natural'Last - 1)
                 and Input'Last <= (Natural'Last - 1) and Input'First <= Natural'Last) 
         then
            Flag := False;
            return Flag;
         else
            k := 1;
            Last_Length := 0;
            I := Input'First;
            if not (Input(I).Offset = 0 and Input(I).Length = 0) then Flag := False; return Flag; end if;
            if Input(I).Offset > Last_Length then Flag := False; return Flag; end if;
            -- If Input is not empty, then the each token in Input Array must be valid
            pragma Assert(Input'Length > 0 and Input(I).Offset <= 0 and Input(I).Length = 0 and I = Input'First and Flag and Valid(Input,I));
            While I >= Input'First and I <= Input'Last loop
               pragma Loop_Invariant
                 (Input'Length > 0 
                  and Input'Length <= (Natural'Last - 1)
                  and Input'Last <= (Natural'Last - 1) and Input'First <= Natural'Last
            --------------------------------------------------------
                  and I >= Input'First and I <= Input'Last + 1 
                  and k >= 1 
                  and (if I > Input'First then (
                       if (Last_Length <= (Natural'Last - Input(I - 1).Length - 1)
                       and (if I - 1 = Input'First then Last_Length = 0)
                       and Input(I - 1).Offset <= Last_Length
                       and (if Input(I - 1).Offset = 0 then Input(I -1).Length = 0)) 
                     then k = Last_Length + Input (I - 1).Length + 1)) 
                    );

               pragma Loop_Invariant (Input'Length = 0 or else True);
               pragma Loop_Invariant (Input'Length > 0 
                                      and then (for all P in Input'First .. Input'Last => 
                                             To_Big_Integer(Input(P).Offset) <=
                                           (if P = Input'First then Zero 
                                              else Length_Acc(Input)(P-1))));
               pragma Loop_Invariant (Input'Length > 0 
                                      and then (for all P in Input'First .. Input'Last =>In_Range(Arg => Length_Acc(Input)(P),
                                 Low => To_Big_Integer(One), High => To_Big_Integer(Integer'Last))));
               pragma Loop_Invariant (Input'Length > 0 
                                      and then (for all P in Input'First .. Input'Last =>(if Input(P).Offset = 0 then Input(P).Length = 0)));
--                 pragma Loop_Invariant (       
--                    Input'Length > 0 and then (for all P in Input'First .. Input'Last =>
--                          In_Range(Arg => Length_Acc(Input)(P),
--                                   Low => To_Big_Integer(One),
--                                   High => To_Big_Integer(Integer'Last)) and
--                       To_Big_Integer(Input(P).Offset) <=
--                       (if P = Input'First then Zero else Length_Acc(Input)(P-1))
--                       and
--                       (if Input(P).Offset = 0 then Input(P).Length = 0)) 
--                    
--                 );
               I := I + 1;
               if I - 1 = Input'First 
               then Last_Length:= 0; 
               else Last_Length := k;
               end if;
               --  pragma Loop_Invariant ((if Error then k=0 else True) and I >= Input'First and I <= Input'Last and Input'Last <= Natural'Last - 1);    
               if not (if Input(I - 1).Offset = 0 then Input(I - 1).Length = 0)
                 or not (Input(I - 1).Offset <= Last_Length and Last_Length <= (Natural'Last - Input(I - 1).Length - 1)) 
               then 
                  Flag := False;
                  return Flag;
               else 
                  k := Last_Length + Input (I - 1).Length + 1;
                  if not (Last_Length < k and k >= 1) 
                  then
                     Flag := False;
                     return Flag; 
                  end if;
               end if;
                
               -- I >= Input'First
            end loop;
         end if;
      else 
         if Input'Length = 0 and Flag then 
            return True;
         else
            Flag := False;
            return Flag;
         end if;
      end if;
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
         k := 0;
         Output_Length := k;
      else
         I := Input'First;
         while I >= Input'First and I <= Input'Last loop
            I := I + 1;
            J := 0;
            while J >= 0 and J <= Input (I - 1).Length - 1 loop
               J := J + 1;
--                 pragma Loop_Invariant (J >= 0 and J <= Input(I - 1).Length and Output'First <= Natural'Last - k - J and To_Big_Integer(Input(I - 1).Offset) <= Length_Acc(Input)(I - 1));
               Output (Output'First + k + J - 1) := Output (Output'First + k - Input (I - 1).Offset + J - 1);    
            end loop;
            Output (Output'First + k + Input (I - 1).Length) := Input (I - 1).Next_C;
            k := k + Input (I - 1).Length + 1;
         end loop;
         Output_Length := k;
      end if;
   end Decode_Fast;

end LZ77;


-- TASK 3:
-- Guarantees offered by writing Decode in Ada: 
-- 1. Strong typing: Ada being a strongly type checked language practically saves from many type-related errors prone in dangerous languages like C. 
-- 2. Range checking: Ada does run time checking on array indexing and arithmetic operations hence preventing out of bound access 
-- and overflow/underflow errors. It solves the buffer overflow vulnerabilities.
-- 3. Safe handling of memory: Ada provides automatic memory management and discards manual
-- memory handling, and thus enhances memory error bugs like null pointer, dangling
-- pointer, and memory leaks. 
-- These properties make Ada implementations much safer and more reliable than dangerous 
-- languages like C, even when the implementation contains bugs. 
-- An Ada implementation can be used where memory safety and error handling matters, 
-- like embedded systems, aviation, and financial applications.

-- Further guarantees offered by formal verification: 
-- 1. Correctness: By formal verification, the implementation is proved to satisfy the specification and behave 
-- correctly according to the pre-conditions and post-conditions stated in the contract. 
-- 2. No runtime errors: Implementation is free from runtime errors as the formal verification proves, including 
-- division by zero, index-out-of-bound, overflow/underflow errors. Hence the level of assurance -- is higher than that which is provided only by runtime checks. 
-- 3. Functional correct solution: Formal verification proves an implementation to output in an expected way for every 
-- valid form of inputs, according to the specified contract. This means the implementation is complete against all the functional requirements. 
-- 4. Invariant preservation: The specification to the formal verification technique is structured so that the preservation of invariants during implementation is guaranteed and will lead to extra safety guarantees during runtime.




-- TASK 6:
-- The Decode_fast only restricts the postcondition of output length should be 
-- equal to the decoded length of the input token array. 

-- Missing condition:
-- 1. Decompressed data should be in the output array and be consistent with
-- the original uncompressed data.
-- Output(Output'First .. Output'First + Output_Length - 1) are identical to 
-- the original bytes b1, b2, ..., bn, where n is the length of the 
-- uncompressed data.

-- 2. For each input token, it should check the format, like the bytes 
-- Output(Output'First + k .. Output'First + k + l - 1) are identical to the bytes 
-- Output(Output'First + k - o .. Output'First + k - o + l - 1), where k is the number of bytes decompressed so far. The byte Output(Output'First + k + l) is equal to c

-- Challenges:
-- 1. Proving the equivalence between compressed and decompressed data: Verifying that the
-- decompressed data matches the original uncompressed data can be challenging, 
-- It may require additional annotations or assertions to establish the equivalence.
-- 2. Dealing with loop invariants and variants: Verifying the correctness of the decompression
-- algorithm often involves reasoning about loops and their invariants. Defining and
-- proving the appropriate loop invariants and variants can be challenging, especially
-- when dealing with complex data dependencies and copying operations.





