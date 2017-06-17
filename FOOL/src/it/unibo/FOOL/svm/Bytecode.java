/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.svm;

/***
 * Excerpted from "Language Implementation Patterns", published by The Pragmatic
 * Bookshelf. Copyrights apply to this code. It may not be used to create
 * training material, courses, books, articles, and the like. Contact us if you
 * are in doubt. We make no guarantees that this code is fit for any purpose.
 * Visit http://www.pragmaticprogrammer.com/titles/tpdsl for more book
 * information.
 ***/

/*
 * Modified by Chun Tian with two more instructs (pconst, aconst) and simplified
 * APIs, now all non-const instructs do not take operands.
 */

public class Bytecode {
    // operand types
    public static final int REG = 0; // unused
    public static final int FUNC = 1;
    public static final int INT = 2;
    public static final int LABEL = 3;
    public static final int POOL = 4;

    public static class Instruction {
	public String name; // E.g., "iadd", "call"
	int[] type = new int[3];
	int n = 0;

	public Instruction(String name) {
	    this(name, 0, 0, 0);
	    n = 0;
	}

	public Instruction(String name, int a) {
	    this(name, a, 0, 0);
	    n = 1;
	}

	public Instruction(String name, int a, int b) {
	    this(name, a, b, 0);
	    n = 2;
	}

	public Instruction(String name, int a, int b, int c) {
	    this.name = name;
	    type[0] = a;
	    type[1] = b;
	    type[2] = c;
	    n = 3;
	}
    }

    // INSTRUCTION BYTECODES (byte is signed; use a short to keep 0..255)
    // @formatter:off
    public static final short INSTR_IADD    = 1;  // integer add
    public static final short INSTR_ISUB    = 2;  // integer sub
    public static final short INSTR_IMUL    = 3;  // integer mul
    public static final short INSTR_ILT     = 4;  // integer less than
    public static final short INSTR_IEQ     = 5;  // integer equal
    public static final short INSTR_FADD    = 6;  // float add
    public static final short INSTR_FSUB    = 7;  // float sub
    public static final short INSTR_FMUL    = 8;  // float mul
    public static final short INSTR_FLT     = 9;  // float less than
    public static final short INSTR_FEQ     = 10; // float eq
    public static final short INSTR_ITOF    = 11; // int to float
    public static final short INSTR_CALL    = 12; // call function
    public static final short INSTR_RET     = 13; // return with/without value
    public static final short INSTR_BR      = 14; // branch
    public static final short INSTR_BRT     = 15; // branch if true
    public static final short INSTR_BRF     = 16; // branch if false
    public static final short INSTR_CCONST  = 17; // push constant char
    public static final short INSTR_ICONST  = 18; // push constant integer
    public static final short INSTR_FCONST  = 19; // push constant float
    public static final short INSTR_SCONST  = 20; // push constant string
    public static final short INSTR_LOAD    = 21; // load from local context
    public static final short INSTR_GLOAD   = 22; // load from global memory
    public static final short INSTR_FLOAD   = 23; // field load
    public static final short INSTR_STORE   = 24; // store in local context
    public static final short INSTR_GSTORE  = 25; // store in global memory
    public static final short INSTR_FSTORE  = 26; // field store
    public static final short INSTR_PRINT   = 27; // print stack top
    public static final short INSTR_ALLOCA  = 28; // push new vector on stack
    public static final short INSTR_NULL    = 29; // push null onto stack
    public static final short INSTR_POP     = 30; // throw away top of stack
    public static final short INSTR_HALT    = 31; // halt machine
    // DYNAMIC INSTRUCTIONS taking operands on stack
    public static final short INSTR_ACONST  = 32; // push constant address
    public static final short INSTR_PCONST  = 33; // push constant pointer
    public static final short INSTR_INVOKE  = 34; // indirect call function
    public static final short INSTR_INDIRECTBR  = 35; // indirect branch
    public static final short INSTR_INDIRECTBRT = 36; // indirect branch if true
    public static final short INSTR_INDIRECTBRF = 37; // indirect branch if false
    public static final short INSTR_DLOAD   = 38; // (d) load from local context
    public static final short INSTR_DGLOAD  = 39; // (d) load from global memory
    public static final short INSTR_DFLOAD  = 40; // (d) field load store in local context
    public static final short INSTR_DSTORE  = 41; // (d) store in local context
    public static final short INSTR_DGSTORE = 42; // (d) store in global memory
    public static final short INSTR_DFSTORE = 43; // (d) field store
    public static final short INSTR_DALLOCA = 44; // (d) push new vector on stack

    // array index is the opcode
    public static Instruction[] instructions = new Instruction[] {
	null, // <INVALID>
	new Instruction("iadd"), // 1
	new Instruction("isub"), // 2 unused
	new Instruction("imul"), // 3
	new Instruction("ilt"),  // 4
	new Instruction("ieq"),  // 5
	new Instruction("fadd"), // 6 unused
	new Instruction("fsub"), // 7 unused
	new Instruction("fmul"), // 8 unused
	new Instruction("flt"),  // 9 unused
	new Instruction("feq"),  // 10 unused
	new Instruction("itof"), // 11 unused
	new Instruction("call",   FUNC),  // 12
	new Instruction("ret"),           // 13
	new Instruction("br",     LABEL), // 14
	new Instruction("brt",    LABEL), // 15
	new Instruction("brf",    LABEL), // 16
	new Instruction("cconst", INT),  // 17 unused
	new Instruction("iconst", INT),  // 18
	new Instruction("fconst", POOL), // 19 unused
	new Instruction("sconst", POOL), // 20 unused
	new Instruction("load",   INT), // 21
	new Instruction("gload",  INT), // 22
	new Instruction("fload",  INT), // 23
	new Instruction("store",  INT), // 24
	new Instruction("gstore", INT), // 25
	new Instruction("fstore", INT), // 26
	new Instruction("print"),       // 27
	new Instruction("alloca", INT), // 28
	new Instruction("null"),        // 29
	new Instruction("pop"),         // 30
	new Instruction("halt"),        // 31
	// DYNAMIC INSTRUCTIONS taking operands on stack
	new Instruction("aconst", LABEL), // 32
	new Instruction("pconst", FUNC),  // 33
	new Instruction("invoke"),        // 34
	new Instruction("indirectbr"),    // 35
	new Instruction("indirectbrt"),   // 36
	new Instruction("indirectbrf"),   // 37
	new Instruction("dload"),   // 38
	new Instruction("dgload"),  // 39
	new Instruction("dfload"),  // 40
	new Instruction("dstore"),  // 41
	new Instruction("dgstore"), // 42
	new Instruction("dfstore"), // 43
	new Instruction("dalloca")  // 44
    };
}
