function Is_Valid(Input : in Token_Array) return Boolean is
   
      k : Natural := 0; --total length

   begin
      
      -- Check if the input array is valid
      ifInput'Length = 0 then  --yes
         return True;
      end if;
         
      -- Iterate through each token in the input
      for I in Input'Range loop

         -- If the first token has a non-zero offset, it is invalid
         if(I = Input'First and Input(I).Offset /= 0 )then  --yes
            return False;
         end if;
         
         -- If the offset of a non-first token is greater than the total length, it is invalid
         if(I /= Input'First and Input(I).Offset > k )then --yes
            return False;
         end if;
  
         -- If the offset is zero and the length is non-zero, it is invalid
         if(Input(I).Offset = 0 and Input(I).Length /=0 )then  --yes
            return False;
         end if;
         
         -- Check if the total length exceeds the maximum value of Integer
         if(Input(I).Length > Integer'Last - k-1)then
            return False;
         end if;
         

         -- Update the total length to include the current token   
         k := k + Input(I).Length + 1 ;
         
         -- Loop invariant to ensure the total length is correct up to the previous token
         pragma Loop_Invariant ( k = (if I = Input'First then 1 else To_Integer(Length_Acc(Input)(I)))  
                                and Valid(Input, I)); 
      
      end loop;    
      
      -- If all checks are passed, the input is valid
      return True;
   
   end Is_Valid;