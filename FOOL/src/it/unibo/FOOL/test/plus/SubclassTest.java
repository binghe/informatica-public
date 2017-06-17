/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test.plus;

import static org.junit.Assert.*;
import java.util.*;
import org.junit.*;
import it.unibo.FOOL.svm.*;
import it.unibo.FOOL.test.*;

/*
 * Test: check subclass relation in assembly code using local precedence lists (lpl)
 * 
 * The idea: if class C1 is a subclass of C2, then the lpl of C1 (e.g. [103 102 101 100])
 * with some head elements removed, must be equal to the lpl of C2 (e.g. [102 101 100]).
 * And the last element (100) is always the same (the class standard_object), because all
 * classes share a single root.
 * 
 * The algorithm:
 * 1. we go through each numbers in the lpl of C1 in a fix-sized loop, until we found one
 *    which is equal to the first number in lpl of C2 (102), and return true.
 * 2. in case we can't find such a number (reach the end of loop), return false.
 * there's no need to check more numbers, because the rest of C1 will be the same as C2.
 */

public final class SubclassTest extends UnitTest {
    @Test
    public void testSubclass() {
	Assembler assem = new Assembler();
	Label restart = assem.newLabel("restart");
	Label success = assem.newLabel("success");
	Label fail = assem.newLabel("fail");
	Label end0 = assem.newLabel("end_of_loop");
	List<Integer> C1_list = Arrays.asList(103, 102, 101, 100, 0);
	List<Integer> C2_list = Arrays.asList(102, 101, 100, 0);
	int x;

	// 1. arguments
	assem.defineDataSize(5);

	int C1 = 0;             // [103 102 101 100 0]
	assem.alloca(C1_list.size());
	assem.gstore(C1);

	x = 0;
	for (int c : C1_list) {
	    assem.iconst(c);
	    assem.gload(C1);
	    assem.fstore(x++); // C1[i] = v
	}

	int C2 = 1;             // [ 102 101 100 0]
	assem.alloca(C2_list.size());
	assem.gstore(C2);

	x = 0;
	for (int c : C2_list) {
	    assem.iconst(c);
	    assem.gload(C2);
	    assem.fstore(x++); // C2[i] = 102
	}

	// 2. initialization
	int i = 2;              // loop variable
	int i_val = 0;
	assem.iconst(i_val);
	assem.gstore(i);

	int e = 3;              // end value
	int e_val = 0;          // type index of root class
	assem.iconst(e_val);
	assem.gstore(e);

	int h = 4;              // head of C2 (102 here)
	assem.gload(C2);
	assem.fload(0);
	assem.gstore(h);

	// 2. end condition
	assem.setLabel(restart);
	assem.gload(C1);
	assem.gload(i);  // load i
	assem.dynamic_fload();  // load C1[i] -- API extension
	assem.gload(e);  // load e
	assem.ieq();       // i == e ?
	assem.brt(fail); // goto end

	// 3. loop body
	assem.gload(C1);
	assem.gload(i);
	assem.dynamic_fload();  // load C1[i] -- API extension
	assem.gload(h);
	assem.ieq();
	assem.brt(success);

	// 4. increase counter
	assem.gload(i);  // load i
	assem.iconst(1); // 1
	assem.iadd();      // i + 1
	assem.gstore(i); // save i

	// 5. restart the loop
	assem.br(restart);

	// 6. return value
	assem.setLabel(success);
	assem.iconst(1); // return true
	assem.br(end0);

	assem.setLabel(fail);
	assem.zero();    // return false
	assem.setLabel(end0);
	assem.halt();
	assem.check();

	Disassembler disasm = new Disassembler(assem);
	disasm.disassemble();
	Interpreter vm = new Interpreter(assem);
	vm.setTrace(true);
	Object retVal = vm.exec();
	assertEquals(retVal, 1);
    }
}
