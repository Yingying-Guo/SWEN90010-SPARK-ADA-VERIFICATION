with Interfaces;
with Big_Integers; use Big_Integers;

package LZ77 with
 SPARK_Mode
is

  -- -----------------------------------------------------------------------
  -- Basic Data Types
  -- -----------------------------------------------------------------------

  -- an array of decompressed data: bytes aka characters
  type Byte_Array is array (Positive range <>) of Character;

  -- a token in the LZ77 compressed data
  type Token is record
    Offset : Natural;
    Length : Natural;
    Next_C : Character;
  end record;

  -- compressed data is an array of tokens
  type Token_Array is array (Positive range <>) of Token;

  -- -----------------------------------------------------------------------
  -- Specification Ingredients
  -- -----------------------------------------------------------------------

  -- to specify the length of the data once it is uncompressed, we use an array
  -- of partial sums (computed below by the Length_Acc ghost function).
  -- This sum is specified over mathematical integers (Big_Integers)
  -- See Lecture 18 (Monday May 9) for explanations of these concepts
  type Partial_Length is array (Positive range <>) of Big_Integer with
   Ghost;

  One : constant Integer := 1 with
   Ghost;

  -- given some compressed data, this specifies how to compute the length of
  -- the uncompressed data, producing an array where the ith entry in the array
  -- specifies the length of the uncompressed data after the ith token has
  -- been decoded, i.e. producing an array of partial sums.
  -- Naturally, the length only gets (strictly) larger as each token is
  -- decoded.
  function Length_Acc (Input : in Token_Array) return Partial_Length with
   Ghost, Pre => Input'Length > 0,
   Post       =>
    Length_Acc'Result'Length = Input'Length
    and then Length_Acc'Result'First = Input'First
    and then
    (for all I in Input'Range =>
      Length_Acc'Result (I) =
      (if I = Input'First then Zero else Length_Acc'Result (I - 1)) +
       To_Big_Integer (Input (I).Length) + To_Big_Integer (One)
      and then
      (for all J in Input'First .. I - 1 =>
        Length_Acc'Result (I) > Length_Acc'Result (J)));

  -- specifies the final decompressed length of some compressed data
  function Decoded_Length (Input : in Token_Array) return Big_Integer with
   Ghost;

  function Decoded_Length (Input : in Token_Array) return Big_Integer is
   (if Input'Length = 0 then Zero else Length_Acc (Input) (Input'Last));

  -- specifies a suitable precondition that allows data to be safely
  -- decompressed, provided the output buffer the data is being decompressed
  -- into is also large enough
  -- specifically, this says that all tokens from Input'First .. Upto can be
  -- safely decompressed
  function Valid
   (Input : in Token_Array; Upto : in Integer) return Boolean with
   Ghost;

  function Valid (Input : in Token_Array; Upto : in Integer) return Boolean is
   (Upto <= Input'Last
    and then
    (Input'Length = 0
     or else
     (for all I in Input'First .. Upto =>
       In_Range
        (Arg  => Length_Acc (Input) (I), Low => To_Big_Integer (One),
         High => To_Big_Integer (Integer'Last)) and
       To_Big_Integer (Input (I).Offset) <=
        (if I = Input'First then Zero else Length_Acc (Input) (I - 1)) and
       (if Input (I).Offset = 0 then Input (I).Length = 0))));

  -- -----------------------------------------------------------------------
  -- Code
  -- -----------------------------------------------------------------------

  -- print out a token (e.g. for debugging purposes)
  procedure Put (T : in Token);

  -- attempt to decode compressed data from the 'Input' array, placing the
  -- uncompressed data into the 'Output' array. When successful,
  -- 'Output_Length' indicates the length of the decompressed data and
  -- 'Error' should be set to False.
  -- When an error occurs, 'Error' should be set to True and
  -- 'Output_Length' should be set to 0.
  procedure Decode
   (Input         : in     Token_Array; Output : in out Byte_Array;
    Output_Length :    out Natural; Error : out Boolean) with
   Post => (if Error then Output_Length = 0 else True);

  -- determine whether the compressed data in 'Input' can be safely
  -- decompressed, assuming the output buffer is large enough
  function Is_Valid (Input : in Token_Array) return Boolean with
   Post =>
    (if Is_Valid'Result then Valid (Input, Input'Last)
     else not Valid (Input, Input'Last));

  -- an implementation of Decode that uses design by contract to assume in its
  -- precondition that the data can be safely decompressed. It therefore does
  -- not need to indicate whether it succeeded or not (since it will always
  -- succeed, assuming its precondition holds). Its implementation also does
  -- not need to perform any checks on the compressed data and can just
  -- blindly decompress it without having to worry about potential errors
  -- like indexing an arry out of bounds or integer overflow; hence it is
  -- faster than Decode above. This is an instance in which we use formal
  -- verification to help us write faster code than we could have written
  -- without verification!
  procedure Decode_Fast
   (Input         : in     Token_Array; Output : in out Byte_Array;
    Output_Length :    out Natural) with
   Pre  =>
    Valid (Input, Input'Last)
    and then Output'Length >= To_Integer (Decoded_Length (Input)),
   Post => Output_Length = To_Integer (Decoded_Length (Input));
end LZ77;
