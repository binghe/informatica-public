#A Formalization of the Process Algebra CCS in HOL4
### by Chun Tian

based on «A formalization of the process algebra CCS in high order logic» by Prof. Monica Nesi <monica.nesi@univaq.it>

The following is a brief listing of what's available in the distribution.

     CCS-Nesi/             * Old HOL88 proof scripts (from Prof. Monica Nesi)
     
     CCSScript.sml         * Basic definitions and theorems of CCS processes
     CCSLib.{sml|sig}      * General utilities used in all proof scripts
     CCSSyntax.{sml|sig}   * Programming interfaces for CCS processes
     CCSSimps.{sml|sig}    * Decision procedure for computing CCS transitions
     StrongEQScript.sml    * Definition and basic results of strong equivalence
     StrongEQLib.{sml|sig} * Library for tacticals and functions for strong equivalance
     StrongLaws.sml        * Strong equivalence laws for CCS processes
     WeakEQScript.sml      * Definition and minimal results of weak equivalence 
     ExampleScript.sml     * Example code used in project reports
     
     Holmakefile           * Makefile for building the HOL theories
     
     hol-ccs.pdf           * The main project paper
     references.pdf        * All theorems and definitions in PDF
