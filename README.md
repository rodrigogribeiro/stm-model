A property testing based approach for software transactional memory safety
==================

Test suite
---------

We use Quickcheck, to generate random TM programs and 
and check the resulting histories againts the opacity property.


Executing the test suite
----------------
 
To execute the test suite you will need the [Haskell stack tool](https://docs.haskellstack.org/en/stable/README/).
Having it installed, you will need to set-up the environment. For this, execute:

     stack setup
     
This command will install all necessary libraries and the GHC compiler, if needed.
With a proper environment configured, just execute:


     stack test 
     
to run the test suite. Currently, the test suite generates 1000 random programs. 
To change this number, just modify the file test/Spec.hs.

Building the paper
---------------

The paper "A property testing based approach for software transactional memory safety" is a literate 
Haskell file that can be pre-processed using [lhs2TeX](https://hackage.haskell.org/package/lhs2tex). 
A makefile that builds the paper is avaliable at folder papers/sblp2018/paper. 


Code coverage results
-------------

The coverage of our test suite can be produced using the command 

     stack test --coverage

which will generate a html report.
