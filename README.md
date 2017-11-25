# BigSML
A library for arbitrary precision floating-point numbers in SML.

Tested with Standard ML of New Jersey v110.81.
This was coded only for fun, no improvements are planned.

Numbers are represented by a 4-tuple consisting of:
- Maximum precision (or Unlimited)
- Sign
- Integer exponent
- List of decimal digits, the first of which represents the integer part of the number

## Supported operations:

- Addition (add);
- Unary (minus) and binary (sub) subtraction;
- Multiplication (multl)
- Division (divide)
- Square Root (sqrt)

Division and square root are calculated using the Newton-Raphson method

## Notable ommissions:

- Floor
- Ceiling
- Conversion to/from real
- Conversion to/from IntInf

Contributions are welcome. Enjoy :)
