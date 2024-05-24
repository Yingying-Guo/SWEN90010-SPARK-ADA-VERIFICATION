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
      -- Store the length of last decompressed temporary output array
      Last_Length : Natural;
      -- Tracks the number of bytes processed and Store the length of decompressed temporary output array
      k           : Natural := 0;
   begin
      Error := False;
      -- Check for empty Input and Output and when accessing the Input or Output array
      if not(Input'Length >= 0 and Output'Length >= 0)
      then
         k             := 0;
         Output_Length := k;
         Error         := True;
         return;
      end if;
         -- If Input is not empty, then each token in the Input Array must be valid
         for I in Input'First .. Input'Last loop  
             -- Check for the current position k is within the range of the Output array after considering the length of the current token in the Input array
             -- and also the calculation not cause Integer overflow
             if  not (k <= (Output'Length - Input (I).Length - 1)
               -- Check for the offset of the token is valid
--                 and (if Input (I).Offset > 0 then Input (I).Length > 0) 
               and Input (I).Offset <= k)
             then
               -- If any of the above conditions are not met, set k to 0, Output_Length to k and Error to True, then return
               k             := 0;
               Output_Length := k;
               Error := True;          
               return;
            else
               -- Byte-by-byte copying based on the current token
               -- Token (o, l, c):
               -- the bytes bk+1,. . . , bk+1+(l-1) are identical to the bytes bk+1-o,. . . , bk+1+(l-1)-o,
               -- the bytes bk+1,. . . , bk+l       are identical to the bytes bk+1  ,. . . , bk+l-o,
               -- byte bk+1+l is c
               for J in 0 .. Input (I).Length - 1 loop
                  -- Copy the byte from the offset position to the current position
                  Output (Output'First + k + J) := Output (Output'First + k - Input (I).Offset + J);
                  
                  pragma Loop_Invariant(Output (Output'First + k + J) = Output(Output'First + k - Input (I).Offset + J));
               
               end loop;
               -- Set the next byte to the next character in the Input
               Output (Output'First + k + Input (I).Length) := Input (I).Next_C;
               -- Update Last_Length and k
               Last_Length := k;
               k := Last_Length + Input (I).Length + 1;
            end if;
            
            pragma Loop_Invariant
              (if Error then k = 0 else
                  (Output(Output'First + Last_Length + Input (I).Length) = Input (I).Next_C 
                       and k = Last_Length + Input (I).Length + 1));

         end loop;
         -- when there is not error set Output_Length to k, where k indicates the length of the decompressed data
         Output_Length := k;
      
   end Decode;

   function Is_Valid (Input : in Token_Array) return Boolean is
      k           : Natural;
      Last_Length : Natural;
      Flag        : Boolean := True;
   begin
--    check the length of the input array
      if Input'Length = 0 then return Flag; end if;

      if Input'Length < 0 then Flag := False; return Flag; end if;
      
      k := 0;

      -- If Input is not empty, then the each token in Input Array must be valid
      for I in Input'First ..  Input'Last loop
         -- update the cumulative length
         Last_Length := k;
         -- exit when I > Input'Last;
         -- check the current token is valid -> won't cause integer overflow
         if Natural'Last - Input(I).Length - 1 < Last_Length then Flag := False; return Flag; 
         end if;
         -- update the length after decompress
         k := Last_Length + Input(I).Length + 1;
         -- check the k is valid
         if k < 1 or k <= Last_Length then Flag := False; return Flag; end if;
         -- check the offset of current token 
         if Input (I).Offset = 0 and Input (I).Length /= 0 then Flag := False; return Flag; end if;
         if Input (I).Offset > Last_Length then Flag := False; return Flag; end if;
         
         pragma Loop_Invariant(k <= Natural'Last);
         -- Loop Invariants to ensure that the structural properties of the Input array are correct and stable:
         -- 1. Input'Length > 0 ensures the loop is processing a non-empty array.
         -- 2. Input'Last <= Natural'Last and Input'First <= Natural'Last ensure that the indices of the array are within the valid range for the type Natural, preventing any range violation errors.
         pragma Loop_Invariant
            (Input'Length > 0 and
            Input'Last <= Natural'Last and
            Input'First <= Natural'Last);
         pragma Loop_Invariant (I >= Input'First); 
         -- Loop Invariant to ensure that:
         -- 1. k is always greater than or equal to 1, ensuring that the cumulative length starts valid and grows.
         -- 2. k does not exceed the maximum integer size to prevent overflow errors.            
         -- 3. If I is not the first index, it checks whether the length from the previous token plus one (for the current token)
         pragma Loop_Invariant
            (k >= 1 and k <= Integer'Last and
            (if I > Input'First then
               (if (Last_Length <= (Natural'Last - Input (I).Length - 1) and (if I = Input'First then Last_Length = 0))
                  then k = Last_Length + Input (I).Length + 1)));
         
         pragma Loop_Invariant (k = (if I = Input'First then 1 else To_Integer(Length_Acc(Input)(I)))  
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
   begin
      for I in Input'First .. Input'Last loop
         for J in 0 .. Input (I).Length - 1 loop
            Output (Output'First + k + J) :=  Output (Output'First + k - Input (I).Offset + J);
         end loop;
         Output (Output'First + k + Input (I).Length) := Input (I).Next_C;
         k := k + Input (I).Length + 1;
         pragma Loop_Invariant (k = (if I = Input'First then 1 else To_Integer(Length_Acc(Input)(I))));
      end loop;
      Output_Length := k;
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





