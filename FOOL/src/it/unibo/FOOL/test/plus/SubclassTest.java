/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test.plus;

import static org.junit.Assert.assertEquals;
import java.util.*;
import org.junit.Test;
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
	Label end = assem.newLabel("end_of_loop");
	List<Integer> C1_list = Arrays.asList(103, 102, 101, 100, 0);
	List<Integer> C2_list = Arrays.asList(102, 101, 100, 0);
	int x;

	// 1. arguments
	assem.defineDataSize(5);

	int C1 = 0;             // [103 102 101 100 0]
	assem.gen("struct", C1_list.size());
	assem.gen("gstore", C1);

	x = 0;
	for (int c : C1_list) {
	    assem.gen("iconst", c);
	    assem.gen("gload", C1);
	    assem.gen("fstore", x++); // C1[i] = v
	}

	int C2 = 1;             // [ 102 101 100 0]
	assem.gen("struct", C2_list.size());
	assem.gen("gstore", C2);

	x = 0;
	for (int c : C2_list) {
	    assem.gen("iconst", c);
	    assem.gen("gload", C2);
	    assem.gen("fstore", x++); // C2[i] = 102
	}

	// 2. initialization
	int i = 2;              // loop variable
	int i_val = 0;
	assem.gen("iconst", i_val);
	assem.gen("gstore", i);

	int e = 3;              // end value
	int e_val = 0;          // type index of root class
	assem.gen("iconst", e_val);
	assem.gen("gstore", e);

	int h = 4;              // head of C2 (102 here)
	assem.gen("gload", C2);
	assem.gen("fload", 0);
	assem.gen("gstore", h);

	// 2. end condition
	assem.setLabel(restart);
	assem.gen("gload", C1);
	assem.gen("gload", i);  // load i
	assem.gen("dfload");	// load C1[i] -- API extension
	assem.gen("gload", e);  // load e
	assem.gen("ieq");       // i == e ?
	assem.gen("brt", fail); // goto end

	// 3. loop body
	assem.gen("gload", C1);
	assem.gen("gload", i);
	assem.gen("dfload");	// load C1[i] -- API extension
	assem.gen("gload", h);
	assem.gen("ieq");
	assem.gen("brt", success);

	// 4. increase counter
	assem.gen("gload", i);  // load i
	assem.gen("iconst", 1); // 1
	assem.gen("iadd");      // i + 1
	assem.gen("gstore", i); // save i

	// 5. restart the loop
	assem.gen("br", restart);

	// 6. return value
	assem.setLabel(success);
	assem.gen("iconst", 1); // return true
	assem.gen("br", end);

	assem.setLabel(fail);
	assem.gen("null");      // return false
	assem.setLabel(end);
	assem.gen("halt");
	assem.check();

	Disassembler disasm = new Disassembler(assem);
	disasm.disassemble();
	Interpreter vm = new Interpreter(assem);
	vm.setTrace(true);
	Object retVal = vm.exec();
	assertEquals(retVal, 1);
    }
}
