/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL;

import java.util.*;
import org.antlr.v4.runtime.tree.*;
import it.unibo.FOOL.FOOLParser.*;
import it.unibo.FOOL.env.*;
import it.unibo.FOOL.svm.*;

/**
 * Code generation phase
 */

public class EmitPhase extends FOOLBaseVisitor<ParseTree> {
    List<GenericFunction> gf_list = new LinkedList<GenericFunction>();
    ParseTreeProperty<Scope> scopes;
    ParseTreeProperty<Type> types;
    GlobalScope globals;
    Scope currentScope;
    Assembler assem;
    int dataSize = 0;
    int top_locals = 0; // for top-level let binding
    boolean on_error = false;
    boolean tail_rec = true;
    boolean need_runtime = false;

    public EmitPhase(TypePhase typ) {
	scopes = typ.scopes;
	types = typ.types;
	globals = typ.globals;
	polys = typ.polys;
	currentScope = globals;
	assem = new Assembler();
    }

    // @formatter:off
    public Assembler getAssembly() { return assem; } // @formatter:on

    public ParseTree visitLetInExp(FOOLParser.LetInExpContext ctx) {
	currentScope = scopes.get(ctx);
	ParseTree body = visitChildren(ctx);
	Scope s = currentScope.getEnclosingScope();
	// special treatment for top-level LET binding
	if (s.getScopeName() == "global") {
	    // take the maximal if there're multiple top-level LET bindings
	    top_locals = Math.max(top_locals, currentScope.getNextID());
	    System.out.println("nlocals for top-level LET: " + top_locals);
	}
	currentScope = s;
	return body;
    }

    public ParseTree visitIntVal(FOOLParser.IntValContext ctx) {
	ParseTree body = visitChildren(ctx);
	int i = Integer.valueOf(ctx.getText());
	assem.iconst(i);
	return body;
    }

    public ParseTree visitBoolVal(FOOLParser.BoolValContext ctx) {
	ParseTree body = visitChildren(ctx);
	String text = ctx.getText();
	if (text.equals("true"))
	    assem.iconst(1);
	else
	    assem.zero();
	return body;
    }

    public ParseTree visitPrintExp(FOOLParser.PrintExpContext ctx) {
	ParseTree body = visitChildren(ctx);
	assem.print();
	return body;
    }

    public ParseTree visitFactor(FOOLParser.FactorContext ctx) {
	ParseTree body = visitChildren(ctx);
	Type right = types.get(ctx.right);
	if (right != null) assem.ieq();
	return body;
    }

    public ParseTree visitTerm(FOOLParser.TermContext ctx) {
	ParseTree body = visitChildren(ctx);
	Type right = types.get(ctx.right);
	if (right != null) assem.imul();
	return body;
    }

    public ParseTree visitExp(FOOLParser.ExpContext ctx) {
	ParseTree body = visitChildren(ctx);
	Type right = types.get(ctx.right);
	if (right != null) assem.iadd();
	return body;
    }

    public ParseTree visitIfExp(FOOLParser.IfExpContext ctx) {
	Label L1 = assem.newLabel("else");
	Label L2 = assem.newLabel("endif");
	visit(ctx.cond);	// gen(cond)
	assem.zero();	// push 0 (false)
	assem.ieq();	// test if cond is true
	assem.brt(L1);	// if not, go to L1 (else)
	visit(ctx.thenBranch);	// gen(then)
	assem.br(L2);	// goto L2 (endif)
	assem.setLabel(L1);	// else:
	visit(ctx.elseBranch);	// gen(else)
	assem.setLabel(L2);	// endif
	return ctx;
    }

    public ParseTree visitGlobalVar(FOOLParser.GlobalVarContext ctx) {
	FOOLParser.VarasmContext varasm = ctx.varasm();
	String name = varasm.vardec().ID().getText();
	VariableSymbol var = (VariableSymbol) globals.resolve(name);
	int index = var.getID();
	visit(varasm.exp());
	assem.gstore(index);
	dataSize++;
	return ctx;
    }

    /* Code generation of variable definitions */
    public ParseTree visitVarAssignment(FOOLParser.VarAssignmentContext ctx) {
	FOOLParser.VarasmContext varasm = ctx.varasm();
	String name = varasm.vardec().ID().getText();
	VariableSymbol var = (VariableSymbol) currentScope.resolve(name);
	int index = var.getID();
	visit(varasm.exp());
	assem.store(index);
	return ctx;
    }

    /* Code generation of variable references */
    public ParseTree visitVarExp(FOOLParser.VarExpContext ctx) {
	String name = ctx.ID().getText();
	VariableSymbol sym = (VariableSymbol) currentScope.resolve(name);
	assert (sym != null);

	int index = sym.getID();
	if (sym.getScope().getScopeName() == "global")
	    assem.gload(index);
	else
	    assem.load(index);
	return ctx;
    }

    public List<Type> getTypes(List<ExpContext> args) {
	Iterator<ExpContext> iter = args.iterator();
	List<Type> argTypes = new LinkedList<Type>();
	while (iter.hasNext()) {
	    ExpContext exp = iter.next();
	    argTypes.add(types.get(exp));
	}
	return argTypes;
    }

    public void set_tail_rec(boolean flag) {
	tail_rec = flag;
    }

    /* Code generation of function definitions */
    public ParseTree visitFun(FOOLParser.FunContext ctx) {
	currentScope = scopes.get(ctx);
	MethodSymbol fun = (MethodSymbol) currentScope;
	int nargs = fun.getNextID(); // scope args + local args
	int nargs2 = fun.nargs();    // local args only
	int nargs1 = nargs - nargs2; // scope args only
	int nlocals = fun.nlocals();
	String name = fun.getName();
	Label begin_of_fun = assem.newLabel("begin_" + name);
	Label end_of_fun = assem.newLabel("end_" + name);
	String cname = assem.newFunctionName(name);
	fun.set_cname(cname);

	assem.br(end_of_fun); // jump directly to the end of function
	assem.defineFunction(cname, nargs, nlocals);
	assem.setLabel(begin_of_fun);
	System.out.printf("emiting function %s [nargs: %d(%d+%d), nlocals: %d]\n", cname, nargs, nargs1, nargs2,
		nlocals);
	ParseTree body = visit(ctx.body()); // generate function body
	// do tail recursion optimization before return
	if (tail_rec) {
	    tail_recursion_optimization(cname, nargs, begin_of_fun);
	}
	assem.ret();
	assem.setLabel(end_of_fun);  // jumped here

	// leave the method scope and go one step higher
	currentScope = currentScope.getEnclosingScope();

	// generating generic function after its first method
	GenericFunction gf = fun.genericFunction();
	if (!gf_list.contains(gf)) {
	    gf_list.add(gf);
	}
	// gf's emit name must be decided here
	String gfName = gf.cname();
	if (gfName == null) {
	    gfName = assem.newFunctionName(gf.getName());
	    gf.set_cname(gfName);
	}
	return body;
    }

    /**
     * Tail recursion optimization: if the last instruct is a call to current
     * function, then instead of calling itself, just jump to the beginning of
     * the function (before storing stack args back to frame).
     */
    public void tail_recursion_optimization(String name, int nargs, Label begin_of_fun) {
	byte[] code = assem.getMachineCode();
	int last_ip = assem.getLastIP();
	int opcode = code[last_ip];
	Bytecode.Instruction I = Bytecode.instructions[opcode];
	if (I.name == "call") {
	    int f = Assembler.getInt(code, last_ip + 1);
	    int g = assem.getConstantPoolIndex(new Function(name));
	    if (f == g) { // if it's the same function
		assem.resetIP(last_ip);
		// 1. store stack args back to frame
		for (int i = nargs - 1; i >= 0; i--)
		    assem.store(i);
		// 2. do branch() instead of call()
		assem.br(begin_of_fun);
		// 3. update all labels at next ip (code[last_ip+5])
		List<Label> labels = assem.getLabels();
		for (Label l : labels) {
		    if (l.address == last_ip + 5) {
			l.address += nargs * (assem.use_indirect() ? 6 : 5);
			l.resolveForwardReferences(code);
		    }
		}
	    }
	}
    }

    /* Code generation of function calls */
    public ParseTree visitFunExp(FOOLParser.FunExpContext ctx) {
	String name = ctx.ID().getText();
	GenericFunction gf = (GenericFunction) currentScope.resolve(name);
	List<ExpContext> args = ctx.exp();
	List<Type> argTypes = this.getTypes(args);

	// lookup the most specific method
	MethodSymbol fun = gf.findMethod(argTypes);
	int last_id = fun.getNextID();
	int base_id = last_id - fun.nargs();

	// 1. push scope arguments
	for (int id = 0; id < base_id; id++)
	    assem.load(id);
	// 2. push local arguments, boxing args when gf is called
	if (getPoly(ctx)) {
	    for (ExpContext e : ctx.exp()) {
		visit(e);
		Type typ = types.get(e);
		// boxing all primitive types before calling gf
		if (typ instanceof BuiltinTypeSymbol) {
		    assem.iconst(typ.getTypeIndex());
		    assem.call(new Function("_box"));
		}
	    }
	    assem.call(new Function(gf.cname()));
	    gf.setCalled(true);
	} else {
	    for (ExpContext e : ctx.exp())
		visit(e);
	    assem.call(new Function(fun.cname()));
	}
	return ctx;
    }

    // @formatter:off
    public boolean on_error() { return on_error; } // @formatter:on

    /**
     * Below are special code for the object-oriented features (FOOL+)
     */
    ParseTreeProperty<Boolean> polys;

    protected boolean getPoly(ParseTree ctx) {
	Boolean p = polys.get(ctx);
	return (p != null) ? p : false;
    }

    public ParseTree visitProg(FOOLParser.ProgContext ctx) {
	ParseTree body = visitChildren(ctx);
	assem.halt();
	assem.defineDataSize(dataSize);
	assem.setLocals(top_locals);

	// code for dynamic dispatching
	for (GenericFunction gf : gf_list)
	    if (gf.called()) this.emit(gf);
	emit_runtime_library();
	assem.check();
	return body;
    }

    public ParseTree visitDefcls(FOOLParser.DefclsContext ctx) {
	// 1. skip the whole class definition
	Label end_of_def = assem.newLabel("end_of_def");
	assem.br(end_of_def); // jump directly to the end

	// 2. generate init function
	assert (currentScope == globals);
	String className = ctx.ID().getText();
	ClassSymbol cls = (ClassSymbol) globals.resolve(className);
	MethodSymbol init = (MethodSymbol) cls.initFunction();
	String name = init.getName();
	String initName = assem.newFunctionName(name);
	init.set_cname(initName);
	int nargs = init.getNextID();
	int nlocals = 0;
	assem.defineFunction(initName, nargs, nlocals);
	currentScope = init;

	// (optionally) call init function of super classes
	FOOLParser.SupersContext p = ctx.supers();
	if (p != null) visit(p);

	// (optionally) initialize local slots
	FOOLParser.SlotsContext s = ctx.slots();
	if (s != null) {
	    visit(ctx.slots());
	}
	assem.ret(); // no return value

	// 3. generate the new() function
	generate_new(cls);

	// 4. set ending label
	assem.setLabel(end_of_def); // jumped here
	currentScope = globals;
	return ctx;
    }

    /*
     * the assembly code involved when new() is called for creating a new class
     */
    protected void generate_new(ClassSymbol cls) {
	MethodSymbol init = (MethodSymbol) cls.initFunction();
	MethodSymbol nf = (MethodSymbol) cls.newFunction();
	String name = nf.getName();
	String nfName = assem.newFunctionName(name);
	nf.set_cname(nfName);
	int nargs = nf.getNextID();
	int nlocals = 1;
	assem.defineFunction(nfName, nargs, nlocals);

	// filling class precedence list into index 0 and return the
	List<ClassSymbol> list = cls.getLocalPrecedenceList();
	int temp = nargs + nlocals - 1;
	int n = list.size() + 1; // the last place is for 0
	assem.alloca(n);  // create a new struct holding the list
	assem.store(temp);
	int i = 0;
	for (ClassSymbol c : list) {
	    assem.iconst(c.getTypeIndex());
	    assem.load(temp);  // load class precedence list
	    assem.fstore(i++); // store one index into the list
	}
	assem.zero();
	assem.load(temp);
	assem.fstore(i);  // append 0 at last
	assem.load(temp); // load class precedence list
	assem.load(0);    // load object
	assem.fstore(0);  // store the list into object[0]

	// push the arguments and call _init()
	for (i = 0; i < nargs; i++)
	    assem.load(i);
	assem.call(new Function(init.cname()));
	assem.load(0);
	assem.ret(); // return the object
    }

    public ParseTree visitSupers(FOOLParser.SupersContext ctx) {
	// 1. get parent class and its init function
	String name = ctx.ID().getText();
	ClassSymbol cls = (ClassSymbol) globals.resolve(name);
	MethodSymbol fun = (MethodSymbol) cls.initFunction();
	String funName = fun.cname();

	// 2. generate code to call the init function
	assem.load(0); // push the object first
	visitChildren(ctx); // push other arguments
	assem.call(new Function(funName));
	return ctx;
    }

    public ParseTree visitSlotInit(FOOLParser.SlotInitContext ctx) {
	// 1. get slot index
	FOOLParser.VarasmContext varasm = ctx.varasm();
	String name = varasm.vardec().ID().getText();
	ClassSymbol cls = (ClassSymbol) currentScope.getEnclosingScope();
	VariableSymbol var = (VariableSymbol) cls.resolveMember(name);
	int index = var.getID();

	// 2. generate code to store the value into the slot
	visit(varasm.exp());  // push the value
	assem.load(0); // push the object
	assem.fstore(index); // store the value into the slot
	return ctx;
    }

    public ParseTree visitClassExp(FOOLParser.ClassExpContext ctx) {
	// 1. get current class and its init function
	String name = ctx.ID().getText();
	ClassSymbol cls = (ClassSymbol) currentScope.resolve(name);
	MethodSymbol nf = cls.newFunction();
	String nfName = nf.cname();
	int nslots = cls.getNextID();

	// 2. generate code to create an object and call its init function
	assem.alloca(nslots);
	visitChildren(ctx);
	assem.call(new Function(nfName));
	return ctx;
    }

    public ParseTree visitMethodExp(FOOLParser.MethodExpContext ctx) {
	ValueContext object = ctx.value();
	TerminalNode method = ctx.ID();
	// 1. get method symbol
	String name = method.getText();
	GenericFunction gf = (GenericFunction) currentScope.resolve(name);
	List<ExpContext> args = ctx.exp();
	List<Type> argTypes = new ArrayList<Type>();
	argTypes.add(types.get(object));
	argTypes.addAll(getTypes(args));
	MethodSymbol fun = gf.findMethod(argTypes);

	int last_id = fun.getNextID();
	int base_id = last_id - fun.nargs();
	// 2. push scope arguments
	for (int id = 0; id < base_id; id++)
	    assem.load(id);
	// 3. push the object
	visit(object);
	// 4. push local arguments
	if (getPoly(ctx)) {
	    for (ExpContext e : ctx.exp()) {
		visit(e);
		Type typ = types.get(e);
		// boxing all primitive types before calling gf
		if (typ instanceof BuiltinTypeSymbol) {
		    assem.iconst(typ.getTypeIndex());
		    assem.call(new Function("_box"));
		}
	    }
	    String gfName = gf.cname();
	    assem.call(new Function(gfName));
	    gf.setCalled(true);
	} else {
	    visitChildren(ctx);
	    assem.call(new Function(fun.cname()));
	}
	return ctx;
    }

    public ParseTree visitSlotExp(FOOLParser.SlotExpContext ctx) {
	ValueContext object = ctx.value();
	TerminalNode slot = ctx.ID();
	// 1. get slot index in object layout
	ClassSymbol cls = (ClassSymbol) types.get(object);
	String slotName = slot.getText();
	VariableSymbol var = (VariableSymbol) cls.resolveMember(slotName);
	int slotIndex = var.getID();
	// 2. code generation
	visit(object); // push object
	assem.fload(slotIndex); // push slot (and pop object)
	return ctx;
    }

    /*
     * Another version of GenericFunction.findMethod() written in assembly code,
     * for dynamic method dispatching at runtime. What we have here.
     */
    protected void emit(GenericFunction gf) {
	List<MethodSymbol> methods = gf.findMethods(null);
	List<Label> labels = new LinkedList<Label>();
	String name = gf.getName();
	int m = methods.size(), m0;
	int n = gf.nargs(), n0;
	int nlocals = n + m * n + 1;

	// 0. define a gf, there's no need to jump outside first, because the
	// code will be inserted after "halt".
	String gfName = gf.cname();
	assem.defineFunction(gfName, n, nlocals);
	System.out.printf("emiting new gf %s [nargs: %d, nlocals: %d]\n", gfName, n, nlocals);

	// 1.store the local precedence list of input arguments into local
	// variables, ranged from n+0 to n+(n-1). built-in types are
	// already boxed.
	for (n0 = 0; n0 < n; n0++) {
	    int C1 = n + n0;
	    assem.load(n0);
	    assem.fload(0);
	    assem.store(C1);
	}

	// 2. store the local precedence list of each parameters of all methods
	// into local variables:
	// for the nth arg of the mth method, the index is 2*n + n*m0 + n0,
	// because the first N places were used by function arguments.
	int result = 2 * n + n * m; // holding the chosen method
	Label prepare_return = assem.newLabel("prepare_return");
	m0 = 0;
	for (MethodSymbol method : methods) {
	    Label next_method = assem.newLabel("next_method_" + m0);
	    labels.add(next_method);
	    List<Type> types = method.getTypes();
	    n0 = 0;
	    for (Type t : types) {
		int C1 = n + n0;
		int C2 = 2 * n + n * m0 + n0;
		int x = 0;
		if (t instanceof ClassSymbol) {
		    ClassSymbol cls = (ClassSymbol) t;
		    List<ClassSymbol> lst = cls.getLocalPrecedenceList();
		    assem.alloca(lst.size() + 1);
		    assem.store(C2);
		    for (ClassSymbol c : lst) {
			assem.iconst(c.getTypeIndex());
			assem.load(C2);
			assem.fstore(x++); // C[i] = v
		    }
		} else {
		    assert (t instanceof BuiltinTypeSymbol);
		    assem.alloca(2);
		    assem.store(C2);
		    assem.iconst(t.getTypeIndex());
		    assem.load(C2);
		    assem.fstore(x++);
		}
		assem.zero();
		assem.load(C2);
		assem.fstore(x); // C2[last] = 0
		// check the type of each method against the input argument, the
		// only purpose here is to get the method id, stored into local
		// variable, say: result.
		assem.load(C1);
		assem.load(C2);
		assem.call(new Function("_subclassp"));
		assem.brf(next_method);
		// increase loop var
		n0++; // columns
	    }
	    assem.pconst(new Function(method.getName()));
	    assem.store(result);
	    assem.br(prepare_return);
	    assem.setLabel(next_method);
	    // increase loop var
	    m0++; // lines
	}
	// no applicable method if reached here
	assem.sconst("no applicable method for " + name);
	assem.print();
	assem.pop();
	assem.iconst(-1);
	assem.halt();

	// final, call the target method with builtin typed variables unboxed:
	assem.setLabel(prepare_return);
	for (int i = 0; i < n; i++) {
	    assem.load(i);
	    assem.call(new Function("_unbox"));
	}
	assem.load(result);
	assem.invoke(); // invoke *result -- API extension
	assem.ret();
	need_runtime = true;
    }

    // The runtime library of FOOL+ written in assembly code, it must be
    // attached to the generated byte code, after "halt".
    protected void emit_runtime_library() {
	if (!need_runtime) return;
	emit_subclassp();
	emit_box();
	emit_unbox();
    }

    // The function _subclassp accepts the local precedence list of two classes
    // (C1 and C2) and return true if C1 is subclass of C2. For example, if C1
    // has local precedence list [102; 101; 100; 0] and C2 is [101; 100; 0],
    // then C1 is subclass of C2. Only single-inheritance is supported.
    //
    // Built-in types are supported too, if their local precedence lists are in
    // forms like [a; 0], in which a is the type index of built-in types.
    protected void emit_subclassp() {
	int nargs = 2;
	int nlocals = 3;
	int C1 = 0, C2 = 1;
	Label restart = assem.newLabel("restart");
	Label success = assem.newLabel("success");
	Label fail = assem.newLabel("fail");
	Label end = assem.newLabel("end_subclassp");

	// 1. initialization
	assem.defineFunction("_subclassp", nargs, nlocals);
	int i = nargs + 0;     // loop variable
	assem.iconst(0);
	assem.store(i);
	int e = nargs + 1;     // end value
	assem.iconst(0);       // type index of root class
	assem.store(e);
	int h = nargs + 2;     // head of C2 (102 here)
	assem.load(C2);
	assem.fload(0);
	assem.store(h);

	// 2. end condition
	assem.setLabel(restart);
	assem.load(C1);
	assem.load(i);         // load i
	assem.dynamic_fload(); // load C1[*i] - API extension!
	assem.load(e);         // load e
	assem.ieq();           // i == e ?
	assem.brt(fail);       // goto end

	// 3. loop body
	assem.load(C1);
	assem.load(i);
	assem.dynamic_fload(); // load C1[*i] - API extension!
	assem.load(h);
	assem.ieq();
	assem.brt(success);

	// 4. increase counter
	assem.load(i);         // load i
	assem.iconst(1);       // 1
	assem.iadd();          // i + 1
	assem.store(i);        // save i

	// 5. restart the loop
	assem.br(restart);

	// 6. return value
	assem.setLabel(success);
	assem.iconst(1);       // return true
	assem.br(end);
	assem.setLabel(fail);
	assem.zero();           // return false
	assem.setLabel(end);
	assem.ret();
    }

    // _box(value, type) create a boxed object [[type 0] value]
    protected void emit_box() {
	int nargs = 2, nlocals = 2;
	// indexes in local stack
	int value = 0, type = 1, outer = 2, inner = 3;

	assem.defineFunction("_box", nargs, nlocals);
	assem.alloca(2);       // [_, _]
	assem.store(inner);
	assem.load(type);
	assem.load(inner);
	assem.fstore(0);       // [type _]
	assem.zero();
	assem.load(inner);
	assem.fstore(1);       // [type 0]
	assem.alloca(2);
	assem.store(outer);    // [_, _]
	assem.load(inner);
	assem.load(outer);
	assem.fstore(0);       // [[type 0] _]
	assem.load(value);
	assem.load(outer);
	assem.fstore(1);       // [[type 0] value]
	assem.load(outer);
	assem.ret();
    }

    // The system function _unbox() unbox its arguments and returns the
    // 2nd struct element back.
    // If the input argument is an object [[? non-zero ... 0] ? ? ...],
    // then it's returned directly. The key is to see if the "non-zero" position
    // is zero or not.
    protected void emit_unbox() {
	int nargs = 1;
	int nlocals = 0;
	Label unbox = assem.newLabel("unbox");
	Label end = assem.newLabel("end_of_unbox");

	assem.defineFunction("_unbox", nargs, nlocals);
	assem.load(0);    // load arg
	assem.fload(0);   // load arg[0]
	assem.fload(1);   // load arg[0][1]
	assem.zero();     // push 0
	assem.ieq();      // arg[0][1] == 0 ?
	assem.brt(unbox); // if so, go to unbox
	assem.load(0);    // else load arg
	assem.br(end);
	assem.setLabel(unbox);
	assem.load(0);    // load arg
	assem.fload(1);   // load arg[1]: the boxed value
	assem.setLabel(end);
	assem.ret();
    }
}
