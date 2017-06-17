/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.svm;

/***
 * Excerpted from "Language Implementation Patterns",
 * published by The Pragmatic Bookshelf.
 * Copyrights apply to this code. It may not be used to create training material, 
 * courses, books, articles, and the like. Contact us if you are in doubt.
 * We make no guarantees that this code is fit for any purpose. 
 * Visit http://www.pragmaticprogrammer.com/titles/tpdsl for more book information.
***/

/*
 * Modified by Chun Tian, for programmatically generating assembly code in Java.
 */

import java.util.*;

public class Assembler {
    public static final int INITIAL_CODE_SIZE = 1024;
    // A switch to use all dynamic instructs or not
    boolean use_indirect = false;

    protected Map<String, Integer> instructionOpcodeMapping = new HashMap<String, Integer>();
    protected Map<String, Label> labels = new HashMap<String, Label>();
    protected List<Object> constPool = new ArrayList<Object>();
    protected int ip = 0; // Instruction address pointer; used to fill code
    protected int last_ip;
    protected byte[] code = new byte[INITIAL_CODE_SIZE]; // code memory
    protected int dataSize = 0;
    protected int nlocals = 0;
    protected Function mainFunction = null;
    protected int ninstr = 0;

    public Assembler() {
	Bytecode.Instruction[] instructions = Bytecode.instructions;
	for (int i = 1; i < instructions.length; i++)
	    instructionOpcodeMapping.put(instructions[i].name.toLowerCase(), i);
    }

    // @formatter:off
    public boolean use_indirect() { return use_indirect; }
    public void useIndirect(boolean flag) { use_indirect = flag; }
    public byte[] getMachineCode() { return code; }
    public int getCodeMemorySize() { return ip; }
    public int getDataSize() { return dataSize; }
    public int getLocals() { return nlocals; }
    public int getInstrs() { return ninstr; }
    public Function getMainFunction() { return mainFunction; }
    public void defineDataSize(int n) { dataSize = n; }
    public void setLocals(int n) { nlocals = n; }
    // the ability to change instruction address pointer
    public int getLastIP() { return last_ip; }
    public void resetIP(int i) { ip = i; }

    // @formatter:on
    public Object[] getConstantPool() {
	return constPool.toArray();
    }

    public List<Label> getLabels() {
	List<Label> list = new ArrayList<Label>(labels.values());
	return list;
    }

    protected void ensureCapacity(int index) {
	if (index >= code.length) { // expand
	    int newSize = Math.max(index, code.length) * 2;
	    byte[] bigger = new byte[newSize];
	    System.arraycopy(code, 0, bigger, 0, code.length);
	    code = bigger;
	}
    }

    /* Generate code for an instruction with no operands */
    public void gen(String instrName) {
	Integer opcodeI = instructionOpcodeMapping.get(instrName);
	if (opcodeI == null) {
	    System.err.println("line " + ip + ": Unknown instruction: " + instrName);
	    return;
	}
	int opcode = opcodeI.intValue();
	last_ip = ip; // save the current ip value
	ensureCapacity(ip + 1);
	code[ip++] = (byte) (opcode & 0xFF);
	ninstr++;
    }

    /* Generate code for an instruction with one operand */
    public void gen(String instrName, Object operand) {
	gen(instrName);
	genOperand(operand);
    }

    public void gen(String instrName, Object o1, Object o2) {
	gen(instrName, o1);
	genOperand(o2);
    }

    public void gen(String instrName, Object o1, Object o2, Object o3) {
	gen(instrName, o1, o2);
	genOperand(o3);
    }

    protected void genOperand(Object operand) {
	int v = 0;
	if (operand instanceof Integer)
	    v = ((Integer) operand).intValue();
	else if (operand instanceof Label)
	    v = getLabelAddress((Label) operand);
	else if (operand instanceof Function)
	    v = getConstantPoolIndex(operand);
	else if (operand instanceof String)
	    v = getConstantPoolIndex(operand);
	else
	    System.err.println("line " + ip + ": Unknown operand: " + operand);
	ensureCapacity(ip + 4); // expand code array if necessary
	writeInt(code, ip, v);  // write operand to code byte array
	ip += 4;		// we've written four bytes
    }

    protected int getRegisterNumber(String rs) {
	rs = rs.substring(1); // convert "rN" -> N
	return Integer.valueOf(rs);
    }

    /* After parser is complete, look for unresolved labels */
    public void check() {
	for (String name : labels.keySet()) {
	    Label sym = (Label) labels.get(name);
	    if (sym.isForwardRef) System.err.println("unresolved reference: " + name);
	}
    }

    public Label newLabel(String id) {
	Label sym = (Label) labels.get(id);
	if (sym == null) {
	    Label l = new Label(id); // isDefined: false, isForwardRef: false
	    labels.put(id, l);
	    return l;
	} else
	    return newLabel(id + "'"); // generate new unique labels
    }

    public void setLabel(Label label) {
	String id = label.name;
	Label sym = (Label) labels.get(id);
	assert (label == sym);

	if (sym.isDefined == false) {
	    sym.isDefined = true;
	    sym.address = ip;
	}

	if (sym.isForwardRef) sym.resolveForwardReferences(code);
    }

    /* Compute the code address of a label */
    protected int getLabelAddress(Label label) {
	String id = label.name;
	Label sym = (Label) labels.get(id);
	assert (label == sym);

	if (sym.isDefined == false) {
	    // assume it's a forward code reference; record operand address
	    sym.isForwardRef = true;
	    sym.addForwardReference(ip);
	    return 0; // we don't know the real address yet
	} else
	    return sym.address;
    }

    public int getConstantPoolIndex(Object o) {
	if (constPool.contains(o)) return constPool.indexOf(o);
	constPool.add(o);
	return constPool.size() - 1;
    }

    public String newFunctionName(String name) {
	Function f = new Function(name);
	if (constPool.contains(f))
	    return newFunctionName(name + "'"); // generate new unique names
	else
	    return name;
    }

    public void defineFunction(String name, int args, int locals) {
	Function f = new Function(name, args, locals, ip);
	if (name.equals("main")) mainFunction = f;
	// Did someone referred to this function before it was defined?
	// if so, replace element in constant pool (at same index)
	if (constPool.contains(f))
	    constPool.set(constPool.indexOf(f), f);
	else
	    getConstantPoolIndex(f); // save into constant pool
    }

    protected int getFunctionIndex(String id) {
	int i = constPool.indexOf(new Function(id));
	if (i >= 0) return i; // already in system; return index.
	// must be a forward function reference
	// create the constant pool entry; we'll fill in later
	return getConstantPoolIndex(new Function(id));
    }

    public static int getInt(byte[] memory, int index) {
	int b1 = memory[index++] & 0xFF; // mask off sign-extended bits
	int b2 = memory[index++] & 0xFF;
	int b3 = memory[index++] & 0xFF;
	int b4 = memory[index++] & 0xFF;
	int word = b1 << (8 * 3) | b2 << (8 * 2) | b3 << (8 * 1) | b4;
	return word;
    }

    /*
     * Write value at index into a byte array, highest to lowest byte, left to
     * right.
     */
    public static void writeInt(byte[] memory, int index, int value) {
	memory[index++] = (byte) ((value >> (8 * 3)) & 0xFF);
	memory[index++] = (byte) ((value >> (8 * 2)) & 0xFF);
	memory[index++] = (byte) ((value >> (8 * 1)) & 0xFF);
	memory[index++] = (byte) (value & 0xFF);
    }

    // syntactic sugars to help writing correct assembly @formatter:off
    public void iadd()             { gen("iadd"); }
    public void isub()             { gen("isub"); }
    public void imul()             { gen("imul"); }
    public void ilt()              { gen("ilt"); }
    public void ieq()              { gen("ieq"); }
    public void fadd()             { gen("fadd"); }
    public void fsub()             { gen("fsub"); }
    public void fmul()             { gen("fmul"); }
    public void flt()              { gen("flt"); }
    public void feq()              { gen("feq"); }
    public void itof()             { gen("itof"); }
    public void ret()              { gen("ret"); }
    public void cconst(char c)     { gen("cconst", c); }
    public void iconst(int i)      { gen("iconst", i); }
    public void fconst(float f)    { gen("fconst", f); }
    public void sconst(String s)   { gen("sconst", s); }
    public void print()            { gen("print"); }
    public void zero()             { gen("null"); }
    public void pop()              { gen("pop"); }
    public void halt()             { gen("halt"); }
    public void aconst(Label l)    { gen("aconst", l); }
    public void pconst(Function f) { gen("pconst", f); }
    public void invoke()           { gen("invoke"); }
    public void indirectbr()       { gen("indirectbr"); }  // unused
    public void indirectbrt()      { gen("indirectbrt"); } // unused
    public void indirectbrf()      { gen("indirectbrf"); } // unused
    public void dynamic_load()     { gen("dload"); }       // unused
    public void dynamic_gload()    { gen("dgload"); }      // unused
    public void dynamic_fload()    { gen("dfload"); }
    public void dynamic_store()    { gen("dstore"); }      // unused
    public void dynamic_gstore()   { gen("gstore"); }      // unused
    public void dynamic_fstore()   { gen("fstore"); }      // unused
    public void dynamic_alloca()   { gen("dalloca"); }     // unused
    // @formatter:on

    public void call(Object func) {
	if (use_indirect) {
	    gen("pconst", func);
	    gen("invoke");
	} else
	    gen("call", func);
    }

    public void br(Object label) {
	if (use_indirect) {
	    gen("aconst", label);
	    gen("indirectbr");
	} else
	    gen("br", label);
    }

    public void brt(Object label) {
	if (use_indirect) {
	    gen("aconst", label);
	    gen("indirectbrt");
	} else
	    gen("brt", label);
    }

    public void brf(Object label) {
	if (use_indirect) {
	    gen("aconst", label);
	    gen("indirectbrf");
	} else
	    gen("brf", label);
    }

    public void load(int n) {
	if (use_indirect) {
	    gen("iconst", n);
	    gen("dload");
	} else
	    gen("load", n);
    }

    public void gload(int n) {
	if (use_indirect) {
	    gen("iconst", n);
	    gen("dgload");
	} else
	    gen("gload", n);
    }

    public void fload(int n) {
	if (use_indirect) {
	    gen("iconst", n);
	    gen("dfload");
	} else
	    gen("fload", n);
    }

    public void store(int n) {
	if (use_indirect) {
	    gen("iconst", n);
	    gen("dstore");
	} else
	    gen("store", n);
    }

    public void gstore(int n) {
	if (use_indirect) {
	    gen("iconst", n);
	    gen("dgstore");
	} else
	    gen("gstore", n);
    }

    public void fstore(int n) {
	if (use_indirect) {
	    gen("iconst", n);
	    gen("dfstore");
	} else
	    gen("fstore", n);
    }

    public void alloca(int n) {
	if (use_indirect) {
	    gen("iconst", n);
	    gen("dalloca");
	} else
	    gen("alloca", n);
    }
}
