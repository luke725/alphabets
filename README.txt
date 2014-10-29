Author: Lukasz Wolochowski

This program is a tool for classifying of alphabets with atoms. It is based on my master thesis "Classification of alphabets with atoms" and uses algorithms described in the thesis. This tool can be used as an executable program or from Haskell interactive environment.

Requirements
In order to compile and use this program ghc (Haskell compiler) and cabal is required. Also Haskell libraries are required: base, containers, HaskellForMaths, parallel, cond, mtl. For running tests additional libraries are needed: HUnit, QuickCheck, quickcheck-instances, tasty, tasty-hunit, tasty-quickcheck. The script scripts/subgrps.sh uses bash and GAP software.

Compiling
The program should be compiled using cabal. Run 'cabal configure', 'cabal build', then 'cabal install'.

Using the program.
The executable file 'alphabets' implements three commands: 'all', 'one', and 'sum'. 'All' classifies all alphabets given as an input, 'one' - one alphabet, and 'sum' - sum of all standard alphabets. Alphabets are given as a subgroup of S_n. Example usage:
alphabets one < data/example-single.txt
alphabets all < data/alph6.txt
alphabets sum < data/class6.txt
more data/alph6.txt | alphabets all | alphabets sum
The script 'scripts/subgrps.sh n' generates all alphabets (up to isomorphism) of dimension up to n.

Structure of the directories
The directory src/ contains source code for alphabet, written in Haskell, tests/ contains Haskell unit test, scripts/ contains the scipt 'scripts/subgrps.sh'. The directory data/ contains data files that can be used as an input of the program:
 - 'data/example-single.txt' is an example of a single-orbit alphabet - a possible input of 'alphabets one'
 - 'data/alphN' for N = 3,4,5,6,7,8 contains all single-orbit alphabets of dimension up to N; it is the output of 'scripts/subgrps.sh N'
 - 'data/classN' for N = 3,4,5,6,7,8 contains the classification of all single-orbit alphabets of dimension up to N. It is the output of 'alphabets all < data/alphN' and can be an input of 'alphabets sum'.

In particular, for any N, 'more data/alphN.txt | alphabets all' classifies all single-orbit alphabets of dimension up to N and
'more data/alphN.txt | alphabets all | alphabets sum' answers the question whether the sum of all standard single-orbit alphabets of dimension up to N is standard.
