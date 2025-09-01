# Adapting Vass to current version of Coq/Mathcomp
## Basics
1. derived from https://github.com/pi8027/vass.git
1. adapted to work on current coq/mathcomp versions, as of 8/2025
   - includes use of HB
   - removed many (not all) deprecation warnings
1. some porting/adaptation difficulties still use rather lengthy code. May perform cleanups to reduce this.
1. owes much to list of changes and renamings in https://github.com/math-comp/math-comp/blob/master/CHANGELOG.md

## Concerning copyrights: 
 - see original https://github.com/pi8027

## Compatibility
- tested (*August 2025*) with:
	- The Coq Proof Assistant, version 8.20.1
    - Compiled with OCaml 4.14.2
	- Running on Arm64 / Linux version 6.10.14-linuxkit (root@buildkitsandbox) 


    | component | version |
	| ------------------------- | ---------- |
	| coq-mathcomp-algebra      |     2.4.0  |            
	| coq-mathcomp-ssreflect    |    2.4.0   |
	| coq-hierarchy-builder     |    1.10.0  |     
	



