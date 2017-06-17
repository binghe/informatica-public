/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.svm;

import java.io.*;

/***
 * Excerpted from "Language Implementation Patterns", published by The Pragmatic
 * Bookshelf. Copyrights apply to this code. It may not be used to create
 * training material, courses, books, articles, and the like. Contact us if you
 * are in doubt. We make no guarantees that this code is fit for any purpose.
 * Visit http://www.pragmaticprogrammer.com/titles/tpdsl for more book
 * information.
 ***/

/*
 * Modified by Chun Tian with essential semantic changes
 */

public class Interpreter implements Serializable {
    private static final long serialVersionUID = -7955296519451508416L;
    public static final int DEFAULT_OPERAND_STACK_SIZE = 100;
    public static final int DEFAULT_CALL_STACK_SIZE = 1000;

    int ip; // instruction pointer register
    byte[] code; // byte-addressable code memory.
    int codeSize;
    int dataSize; // needed by disassembler only
    int nlocals; // nlocals for generated main()
    Object[] globals; // global variable space
    protected Object[] constPool;

    /* Operand stack, grows upwards */
    Object[] operands = new Object[DEFAULT_OPERAND_STACK_SIZE];
    int sp = -1; // stack pointer register

    /* Stack of stack frames, grows upwards */
    StackFrame[] calls = new StackFrame[DEFAULT_CALL_STACK_SIZE];
    int fp = -1; // frame pointer register
    Function mainFunction;
    boolean trace = false;
    Disassembler disasm;

    public Interpreter(Assembler assem) {
	code = assem.getMachineCode();
	codeSize = assem.getCodeMemorySize();
	dataSize = assem.getDataSize();
	nlocals = assem.getLocals();
	constPool = assem.getConstantPool();
	mainFunction = assem.getMainFunction();
	globals = new Object[dataSize];
    }

    /* Execute the bytecodes in code memory starting at mainAddr */
    public Object exec() {
	// SIMULATE "call main()"; set up stack as if we'd called main()
	// its number of locals is always zero because all top-level variable
	// bindings were treated as global variables.
	if (mainFunction == null) {
	    mainFunction = new Function("_main", 0, nlocals, 0);
	}
	StackFrame f = new StackFrame(mainFunction, -1);
	calls[++fp] = f;
	ip = mainFunction.address;
	if (trace) System.out.println("Trace:");
	return cpu();
    }

    /* Simulate the fetch-execute cycle */
    protected Object cpu() {
	Object v = null; // some locals to reuse
	int a, b;
	float e, f;
	StructSpace struct;
	int fieldOffset, funcIndexInConstPool;
	int addr = 0, nfields;
	short opcode = code[ip];
	while (opcode != Bytecode.INSTR_HALT && ip < codeSize) {
	    if (trace) trace();
	    ip++; // jump to next instruction or first byte of operand
	    switch (opcode) {
	    case Bytecode.INSTR_IADD:
		a = (Integer) operands[sp - 1]; // 1st opnd 1 below top
		b = (Integer) operands[sp]; // 2nd opnd at top of stack
		sp -= 2; // pop both operands
		operands[++sp] = a + b; // push result
		break;
	    case Bytecode.INSTR_ISUB:
		a = (Integer) operands[sp - 1];
		b = (Integer) operands[sp];
		sp -= 2;
		operands[++sp] = a - b;
		break;
	    case Bytecode.INSTR_IMUL:
		a = (Integer) operands[sp - 1];
		b = (Integer) operands[sp];
		sp -= 2;
		operands[++sp] = a * b;
		break;
	    case Bytecode.INSTR_ILT:
		a = (Integer) operands[sp - 1];
		b = (Integer) operands[sp];
		sp -= 2;
		operands[++sp] = (a < b ? 1 : 0);
		break;
	    case Bytecode.INSTR_IEQ:
		a = (Integer) operands[sp - 1];
		b = (Integer) operands[sp];
		sp -= 2;
		operands[++sp] = (a == b ? 1 : 0);
		break;
	    case Bytecode.INSTR_FADD:
		e = (Float) operands[sp - 1];
		f = (Float) operands[sp];
		sp -= 2;
		operands[++sp] = e + f;
		break;
	    case Bytecode.INSTR_FSUB:
		e = (Float) operands[sp - 1];
		f = (Float) operands[sp];
		sp -= 2;
		operands[++sp] = e - f;
		break;
	    case Bytecode.INSTR_FMUL:
		e = (Float) operands[sp - 1];
		f = (Float) operands[sp];
		sp -= 2;
		operands[++sp] = e * f;
		break;
	    case Bytecode.INSTR_FLT:
		e = (Float) operands[sp - 1];
		f = (Float) operands[sp];
		sp -= 2;
		operands[++sp] = e < f;
		break;
	    case Bytecode.INSTR_FEQ:
		e = (Float) operands[sp - 1];
		f = (Float) operands[sp];
		sp -= 2;
		operands[++sp] = e == f;
		break;
	    case Bytecode.INSTR_ITOF:
		a = (Integer) operands[sp--];
		operands[++sp] = (float) a;
		break;
	    case Bytecode.INSTR_CALL:
		funcIndexInConstPool = getIntOperand();
		call(funcIndexInConstPool);
		break;
	    case Bytecode.INSTR_RET: // result is on op stack
		StackFrame fr = calls[fp--]; // pop stack frame
		ip = fr.returnAddress; // branch to ret addr
		break;
	    case Bytecode.INSTR_BR:
		ip = getIntOperand();
		break;
	    case Bytecode.INSTR_BRT:
		addr = getIntOperand();
		if (operands[sp--].equals(1)) ip = addr;
		break;
	    case Bytecode.INSTR_BRF:
		addr = getIntOperand();
		if (operands[sp--].equals(0)) ip = addr;
		break;
	    case Bytecode.INSTR_CCONST:
		operands[++sp] = (char) getIntOperand();
		break;
	    case Bytecode.INSTR_ICONST:
	    case Bytecode.INSTR_ACONST:
	    case Bytecode.INSTR_PCONST:
		operands[++sp] = getIntOperand(); // push operand
		break;
	    case Bytecode.INSTR_FCONST:
	    case Bytecode.INSTR_SCONST:
		int constPoolIndex = getIntOperand();
		operands[++sp] = constPool[constPoolIndex];
		break;
	    case Bytecode.INSTR_LOAD: // load from call stack
		addr = getIntOperand();
		operands[++sp] = calls[fp].locals[addr];
		break;
	    case Bytecode.INSTR_GLOAD: // load from global memory
		addr = getIntOperand();
		operands[++sp] = globals[addr];
		break;
	    case Bytecode.INSTR_FLOAD:
		fieldOffset = getIntOperand();
		struct = (StructSpace) operands[sp--];
		operands[++sp] = struct.fields[fieldOffset];
		break;
	    case Bytecode.INSTR_STORE:
		addr = getIntOperand();
		calls[fp].locals[addr] = operands[sp--];
		break;
	    case Bytecode.INSTR_GSTORE:
		addr = getIntOperand();
		globals[addr] = operands[sp--];
		break;
	    case Bytecode.INSTR_FSTORE:
		fieldOffset = getIntOperand();
		struct = (StructSpace) operands[sp--];
		v = operands[sp--];
		struct.fields[fieldOffset] = v;
		break;
	    case Bytecode.INSTR_PRINT:
		System.out.println(operands[sp]);
		break;
	    case Bytecode.INSTR_ALLOCA:
		nfields = getIntOperand();
		operands[++sp] = new StructSpace(nfields);
		break;
	    case Bytecode.INSTR_NULL:
		operands[++sp] = 0;
		break;
	    case Bytecode.INSTR_POP:
		--sp;
		break;
	    case Bytecode.INSTR_INDIRECTBR:
		ip = (Integer) operands[sp--];
		break;
	    case Bytecode.INSTR_INDIRECTBRT:
		addr = (Integer) operands[sp--];
		if (operands[sp--].equals(1)) ip = addr;
		break;
	    case Bytecode.INSTR_INDIRECTBRF:
		addr = (Integer) operands[sp--];
		if (operands[sp--].equals(0)) ip = addr;
		break;
	    case Bytecode.INSTR_INVOKE:
		funcIndexInConstPool = (Integer) operands[sp--];
		call(funcIndexInConstPool);
		break;
	    case Bytecode.INSTR_DLOAD: // load from call stack
		addr = (Integer) operands[sp--];
		operands[++sp] = calls[fp].locals[addr];
		break;
	    case Bytecode.INSTR_DGLOAD: // load from global memory
		addr = (Integer) operands[sp--];
		operands[++sp] = globals[addr];
		break;
	    case Bytecode.INSTR_DFLOAD:
		fieldOffset = (Integer) operands[sp--];
		struct = (StructSpace) operands[sp--];
		operands[++sp] = struct.fields[fieldOffset];
		break;
	    case Bytecode.INSTR_DSTORE:
		addr = (Integer) operands[sp--];
		calls[fp].locals[addr] = operands[sp--];
		break;
	    case Bytecode.INSTR_DGSTORE:
		addr = (Integer) operands[sp--];
		globals[addr] = operands[sp--];
		break;
	    case Bytecode.INSTR_DFSTORE:
		fieldOffset = (Integer) operands[sp--];
		struct = (StructSpace) operands[sp--];
		v = operands[sp--];
		struct.fields[fieldOffset] = v;
		break;
	    case Bytecode.INSTR_DALLOCA:
		nfields = (Integer) operands[sp--];
		operands[++sp] = new StructSpace(nfields);
		break;
	    default:
		throw new RuntimeException("invalid opcode: " + opcode + " at ip=" + (ip - 1));
	    }
	    opcode = code[ip];
	}
	return (sp >= 0) ? operands[sp] : null;
    }

    protected void call(int functionConstPoolIndex) {
	Function fs = (Function) constPool[functionConstPoolIndex];
	StackFrame f = new StackFrame(fs, ip);
	calls[++fp] = f; // push new stack frame for parameters and locals
	// move args from operand stack to top frame on call stack
	for (int a = fs.nargs - 1; a >= 0; a--)
	    f.locals[a] = operands[sp--];
	ip = fs.address; // branch to function
    }

    /*
     * Pull off 4 bytes starting at ip and return 32-bit signed int value.
     * Return with ip pointing *after* last byte of operand. The byte-order is
     * high byte down to low byte, left to right.
     */
    protected int getIntOperand() {
	int word = Assembler.getInt(code, ip);
	ip += 4;
	return word;
    }

    // Tracing, dumping, ...
    public void disassemble() {
	disasm.disassemble();
    }

    public void setTrace(boolean flag) {
	trace = flag;
	if (trace) {
	    disasm = new Disassembler(code, codeSize, dataSize, constPool);
	}
    }

    protected void trace() {
	disasm.disassembleInstruction(ip);
	System.out.print("\t\tstack=[");
	for (int i = 0; i <= sp; i++) {
	    Object o = operands[i];
	    System.out.print(" " + o);
	}
	System.out.print(" ]");
	if (fp >= 0) {
	    System.out.print(", calls=[");
	    for (int i = 0; i <= fp; i++)
		System.out.print(" " + calls[i].sym.name);
	    System.out.print(" ]");
	}
	System.out.println();
    }

    public void coredump() {
	if (constPool.length > 0) dumpConstantPool();
	if (globals.length > 0) dumpDataMemory();
	dumpCodeMemory();
    }

    protected void dumpConstantPool() {
	System.out.println("Constant pool:");
	int addr = 0;
	for (Object o : constPool) {
	    if (o instanceof String)
		System.out.printf("%04d: \"%s\"\n", addr, o);
	    else
		System.out.printf("%04d: %s\n", addr, o);
	    addr++;
	}
	System.out.println();
    }

    protected void dumpDataMemory() {
	System.out.println("Data memory:");
	int addr = 0;
	for (Object o : globals) {
	    if (o != null)
		System.out.printf("%04d: %s <%s>\n", addr, o, o.getClass().getSimpleName());
	    else
		System.out.printf("%04d: <null>\n", addr);
	    addr++;
	}
	System.out.println();
    }

    public void dumpCodeMemory() {
	System.out.println("Code memory:");
	for (int i = 0; code != null && i < codeSize; i++) {
	    if (i % 8 == 0 && i != 0) System.out.println();
	    if (i % 8 == 0) System.out.printf("%04d:", i);
	    System.out.printf(" %3d", ((int) code[i]));
	}
	System.out.println();
    }
}
