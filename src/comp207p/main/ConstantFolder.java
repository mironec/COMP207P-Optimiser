package comp207p.main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;
import org.apache.bcel.util.InstructionFinder;


public class ConstantFolder
{
	ClassParser parser = null;
	ClassGen gen = null;
	ConstantPoolGen cpgen = null;
    InstructionFactory instructionFactory = null;

	JavaClass original = null;
	JavaClass optimized = null;

	public ConstantFolder(String classFilePath) {
        try {
            this.parser = new ClassParser(classFilePath);
            this.original = this.parser.parse();
            this.gen = new ClassGen(this.original);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void removeDeadCode(InstructionFinder instructionFinder, InstructionList il){
        instructionFinder.reread();
        Iterator e = instructionFinder.search("GOTO");
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            GOTO gotoInst = ((GOTO)match[0].getInstruction());
            if(gotoInst.getTarget() == match[0].getNext()){
                InstructionHandle next = match[0].getNext();
                try{
                    il.delete(match[0]);
                    break;
                } catch(TargetLostException ex){
                    for (InstructionHandle target : ex.getTargets()) {
                        for (InstructionTargeter t : target.getTargeters()) {
                            t.updateTarget(target, next);
                        }
                    }
                }
            }
            else{
                Iterator e2 = instructionFinder.search("BranchInstruction");
                InstructionHandle closestBacktarget = null;
                int minPos = il.getEnd().getPosition() + 1;
                while(e2.hasNext()){
                    InstructionHandle instructionHandle = ((InstructionHandle[]) e2.next())[0];
                    BranchInstruction instruction = (BranchInstruction) instructionHandle.getInstruction();
                    if(instruction.getTarget().getPosition() < minPos &&
                            instruction.getTarget().getPosition() > match[0].getPosition()){
                        minPos = instruction.getTarget().getPosition();
                        closestBacktarget = instruction.getTarget();
                    }
                }
                if(gotoInst.getTarget().getPosition() > match[0].getPosition() &&
                        minPos <= gotoInst.getTarget().getPosition() &&
                        closestBacktarget != null &&
                        closestBacktarget != match[0].getNext()){  //Forward jump
                    try{
                        il.delete(match[0].getNext(), closestBacktarget.getPrev());
                        break;
                    } catch(TargetLostException ex){
                        ex.printStackTrace();
                    }
                }
                if(gotoInst.getTarget().getPosition() < match[0].getPosition() &&
                        closestBacktarget != match[0].getNext()){ //Back jump
                    if(closestBacktarget == null){ //No jumps to the dead code found, delete everything
                        try{
                            il.delete(match[0].getNext(), il.getEnd());
                            break;
                        } catch(TargetLostException ex){
                            ex.printStackTrace();
                        }
                    }
                    else{
                        try{
                            il.delete(match[0].getNext(), closestBacktarget.getPrev());
                            break;
                        } catch(TargetLostException ex){
                            ex.printStackTrace();
                        }
                    }
                }
            }
        }
    }

    public void simpleFolding(InstructionFinder instructionFinder, InstructionList il){
        Iterator e = instructionFinder.search("((ConstantPushInstruction|LDC|LDC2_W)(ConstantPushInstruction|LDC|LDC2_W)(ArithmeticInstruction))");
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            InstructionHandle value1, value2, op;
            Type instType1, instType2;
            value1 = match[0];
            value2 = match[1];
            op = match[2];
            instType1 = Utils.getPushType(value1.getInstruction(), cpgen);
            instType2 = Utils.getPushType(value2.getInstruction(), cpgen);
            if(! (Utils.isArithmeticType(instType1) && Utils.isArithmeticType(instType2))){
                System.err.println("THAT'S REALLY WEIRD.");
                continue;
            }
            Object constant = Utils.computeBinaryResult(Utils.getPushValue(value1.getInstruction(), cpgen),
                    Utils.getPushValue(value2.getInstruction(), cpgen),
                    (ArithmeticInstruction) op.getInstruction(), cpgen);
            try {
                il.delete(value1, value2);
            } catch(TargetLostException ex){
                for (InstructionHandle target : ex.getTargets()) {
                    for (InstructionTargeter t : target.getTargeters()) {
                        t.updateTarget(target, op);
                    }
                }
            }
            op.setInstruction(instructionFactory.createConstant(constant));
        }
        instructionFinder.reread();
        e = instructionFinder.search("(ConstantPushInstruction|LDC|LDC2_W)(ConstantPushInstruction|LDC|LDC2_W)(IfInstruction)");
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            InstructionHandle value1, value2, op;
            Type instType1, instType2;
            value1 = match[0];
            value2 = match[1];
            op = match[2];
            instType1 = Utils.getPushType(value1.getInstruction(), cpgen);
            instType2 = Utils.getPushType(value2.getInstruction(), cpgen);
            if(! (Utils.isArithmeticType(instType1) && Utils.isArithmeticType(instType2))){
                System.err.println("THAT'S REALLY WEIRD.");
                continue;
            }
            boolean result = Utils.computeIfResult(Utils.getPushValue(value1.getInstruction(), cpgen),
                    Utils.getPushValue(value2.getInstruction(), cpgen),
                    (IfInstruction) op.getInstruction(), cpgen);
            try {
                il.delete(value1, value2);
            } catch(TargetLostException ex){
                for (InstructionHandle target : ex.getTargets()) {
                    for (InstructionTargeter t : target.getTargeters()) {
                        t.updateTarget(target, op);
                    }
                }
            }
            if(result){
                op.setInstruction(new GOTO(((IfInstruction) op.getInstruction()).getTarget()));
            }
            else{
                InstructionHandle nextNode = op.getNext();
                try {
                    il.delete(op);
                } catch(TargetLostException ex){
                    for (InstructionHandle target : ex.getTargets()) {
                        for (InstructionTargeter t : target.getTargeters()) {
                            t.updateTarget(target, nextNode);
                        }
                    }
                }
            }
        }
        instructionFinder.reread();
        e = instructionFinder.search("(ConstantPushInstruction|LDC|LDC2_W)(IFEQ|IFGE|IFGT|IFLE|IFLT|IFNE)");
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            InstructionHandle value, op;
            value = match[0];
            op = match[1];
            boolean result = Utils.computeIfResult(null,
                    Utils.getPushValue(value.getInstruction(), cpgen),
                    (IfInstruction) op.getInstruction(), cpgen);
            try {
                il.delete(value);
            } catch(TargetLostException ex){
                for (InstructionHandle target : ex.getTargets()) {
                    for (InstructionTargeter t : target.getTargeters()) {
                        t.updateTarget(target, op);
                    }
                }
            }
            if(result){
                op.setInstruction(new GOTO(((IfInstruction) op.getInstruction()).getTarget()));
            }
            else{
                InstructionHandle nextNode = op.getNext();
                try {
                    il.delete(op);
                } catch(TargetLostException ex){
                    for (InstructionHandle target : ex.getTargets()) {
                        for (InstructionTargeter t : target.getTargeters()) {
                            t.updateTarget(target, nextNode);
                        }
                    }
                }
            }
        }
        instructionFinder.reread();
        e = instructionFinder.search("(ConstantPushInstruction|LDC|LDC2_W)(ConstantPushInstruction|LDC|LDC2_W)"+Utils.bigCmp);
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            InstructionHandle value1, value2, op;
            Type instType1, instType2;
            value1 = match[0];
            value2 = match[1];
            op = match[2];
            instType1 = Utils.getPushType(value1.getInstruction(), cpgen);
            instType2 = Utils.getPushType(value2.getInstruction(), cpgen);
            if(! (Utils.isArithmeticType(instType1) && Utils.isArithmeticType(instType2))){
                System.err.println("THAT'S REALLY WEIRD.");
                continue;
            }
            int result = Utils.computeCmpResult(Utils.getPushValue(value1.getInstruction(), cpgen),
                    Utils.getPushValue(value2.getInstruction(), cpgen),
                    op.getInstruction());
            try {
                il.delete(value1, value2);
            } catch(TargetLostException ex){
                for (InstructionHandle target : ex.getTargets()) {
                    for (InstructionTargeter t : target.getTargeters()) {
                        t.updateTarget(target, op);
                    }
                }
            }
            op.setInstruction(instructionFactory.createConstant(result));
        }
        instructionFinder.reread();
        e = instructionFinder.search("(ConstantPushInstruction|LDC|LDC2_W)(INEG|LNEG|FNEG|DNEG)");
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            Type instType1;
            instType1 = Utils.getPushType(match[0].getInstruction(), cpgen);
            if(!Utils.isArithmeticType(instType1)){
                System.err.println("THAT'S REALLY WEIRD.");
                continue;
            }
            Object constant = Utils.computeBinaryResult(null,
                    Utils.getPushValue(match[0].getInstruction(), cpgen),
                    (ArithmeticInstruction) match[1].getInstruction(), cpgen);
            try {
                il.delete(match[0]);
            } catch(TargetLostException ex){
                for (InstructionHandle target : ex.getTargets()) {
                    for (InstructionTargeter t : target.getTargeters()) {
                        t.updateTarget(target, match[1]);
                    }
                }
            }
            match[1].setInstruction(instructionFactory.createConstant(constant));
        }
        instructionFinder.reread();
        e = instructionFinder.search("(ConstantPushInstruction|LDC|LDC2_W)(ConversionInstruction)");
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            ConversionInstruction conversionInstruction = (ConversionInstruction) match[1].getInstruction();
            Number toCast = Utils.getPushValue(match[0].getInstruction(), cpgen);
            Object result = Utils.convertObject(conversionInstruction.getType(cpgen), toCast);
            try {
                il.delete(match[0]);
            } catch(TargetLostException ex){
                for (InstructionHandle target : ex.getTargets()) {
                    for (InstructionTargeter t : target.getTargeters()) {
                        t.updateTarget(target, match[1]);
                    }
                }
            }
            match[1].setInstruction(instructionFactory.createConstant(result));
        }
    }

    private class ConstantVarInfo {
        public Object value;
        public int index;
        public int assignPosition;
        public int lastValidPosition;
    }

    private ArrayList<ConstantVarInfo> lookForConstantVariables(InstructionFinder instructionFinder, InstructionList il, MethodGen m) {
        instructionFinder.reread();
        Iterator e = instructionFinder.search("(ConstantPushInstruction|LDC|LDC_W|LDC2_W)"+Utils.bigStore);
        ArrayList<ConstantVarInfo> constantVarInfos = new ArrayList<>();
        while (e.hasNext()) {
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            ConstantVarInfo info = new ConstantVarInfo();
            info.value = Utils.getPushValue(match[0].getInstruction(), cpgen);
            info.assignPosition = match[1].getPosition();
            info.index = ((StoreInstruction) match[1].getInstruction()).getIndex();
            info.lastValidPosition = il.getEnd().getPosition();
            constantVarInfos.add(info);
        }
        /*for(ConstantVarInfo i : constantVarInfos) {
            for (ConstantVarInfo i2 : constantVarInfos) {
                if (i2.index == i.index && i2.lastValidPosition > i.assignPosition && i.assignPosition > i2.assignPosition) {
                    i2.lastValidPosition = i.assignPosition;
                }
            }
        }*/

        /*ArrayList<ConstantVarInfo> toAdd = new ArrayList<>();
        do{
            toAdd.clear();
            for(ConstantVarInfo info : constantVarInfos) {
                e = instructionFinder.search("IINC|StoreInstruction|BranchInstruction");
                int minPos = il.getEnd().getPosition()+1;
                InstructionHandle nearestInstruction = null;
                while (e.hasNext()) {
                    InstructionHandle[] match = (InstructionHandle[]) e.next();
                    if(match[0].getInstruction() instanceof StoreInstruction){
                        if( ((StoreInstruction)match[0].getInstruction()).getIndex() != info.index) continue;
                    }
                    if(match[0].getInstruction() instanceof IINC){
                        if( ((IINC)match[0].getInstruction()).getIndex() != info.index) continue;
                    }
                    if (match[0].getPosition() > info.assignPosition && match[0].getPosition() < minPos){
                        minPos = match[0].getPosition();
                        nearestInstruction = match[0];
                    }
                }
                if(nearestInstruction == null) continue;
                if(info.lastValidPosition < nearestInstruction.getPosition()) continue;
                info.lastValidPosition = nearestInstruction.getPosition();
                if(nearestInstruction.getInstruction() instanceof BranchInstruction){
                    BranchInstruction branchInstruction = ((BranchInstruction)nearestInstruction.getInstruction());
                    if( branchInstruction.getTarget().getPosition() > nearestInstruction.getPosition() ){ //FORWARD JUMP
                        ConstantVarInfo i = new ConstantVarInfo();
                        i.assignPosition = branchInstruction.getTarget().getPosition();
                        i.lastValidPosition = il.getEnd().getPosition();
                        i.index = info.index;
                        i.value = info.value;
                        toAdd.add(i);
                    }
                    else{
                        boolean modifiedVariable = false;
                        Iterator e2 = instructionFinder.search("StoreInstruction|IINC");
                        while(e2.hasNext()){
                            InstructionHandle handle = ((InstructionHandle[])e2.next())[0];
                            if(handle.getInstruction() instanceof StoreInstruction &&
                                    ((StoreInstruction)handle.getInstruction()).getIndex() != info.index) continue;
                            if(handle.getInstruction() instanceof IINC &&
                                    ((IINC)handle.getInstruction()).getIndex() != info.index) continue;
                            if(handle.getPosition() < branchInstruction.getTarget().getPosition()) continue;
                            if(handle.getPosition() > nearestInstruction.getPosition()) continue;
                            modifiedVariable = true;
                            break;
                        }
                        if(!modifiedVariable){
                            ConstantVarInfo i = new ConstantVarInfo();
                            i.assignPosition = branchInstruction.getTarget().getPosition();
                            i.lastValidPosition = nearestInstruction.getPosition();
                            i.index = info.index;
                            i.value = info.value;
                            toAdd.add(i);
                        }
                    }
                    if(nearestInstruction.getInstruction() instanceof IfInstruction){

                    }
                }
            }
            constantVarInfos.addAll(toAdd);
        } while(!toAdd.isEmpty());*/

        e = instructionFinder.search(Utils.bigStore+"|IINC");
        while (e.hasNext()) {
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            int index = -1;
            if(match[0].getInstruction() instanceof StoreInstruction) index = ((StoreInstruction) match[0].getInstruction()).getIndex();
            if(match[0].getInstruction() instanceof IINC) index = ((IINC) match[0].getInstruction()).getIndex();
            for(ConstantVarInfo i : constantVarInfos) {
                if (i.index == index && i.lastValidPosition > match[0].getPosition() && match[0].getPosition() > i.assignPosition) {
                    i.lastValidPosition = match[0].getPosition();
                }
            }
        }

        e = instructionFinder.search("BranchInstruction");
        while (e.hasNext()) {
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            InstructionHandle handle = match[0];
            BranchInstruction instruction = (BranchInstruction) handle.getInstruction();
            for(ConstantVarInfo info : constantVarInfos){
                //if(info.assignPosition > match[0].getPosition()) continue;
                if(info.lastValidPosition >= instruction.getTarget().getPosition()){
                    info.lastValidPosition = instruction.getTarget().getPosition()-1;
                }
            }
        }

        return constantVarInfos;
    }

    private void optimizeConstantLoads(InstructionFinder instructionFinder, InstructionList il, ArrayList<ConstantVarInfo> constantVarInfos){
        Iterator e = instructionFinder.search(Utils.bigLoad);
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            InstructionHandle instructionHandle = match[0];
            LoadInstruction loadInstruction = (LoadInstruction)match[0].getInstruction();

            ConstantVarInfo replaceInfo = null;
            for(ConstantVarInfo info : constantVarInfos){
                if(loadInstruction.getIndex() == info.index &&
                        instructionHandle.getPosition() <= info.lastValidPosition &&
                        instructionHandle.getPosition() >= info.assignPosition){
                    replaceInfo = info;
                    break;
                }
            }
            if(replaceInfo == null) continue;
            instructionHandle.setInstruction(instructionFactory.createConstant(replaceInfo.value));
        }
    }

    private void deleteAllStackHandles(InstructionHandle starter, InstructionList il){
        InstructionHandle lastToDelete = starter;
        InstructionHandle nextNode = starter.getNext();
        int toDelete = 0;
        do{
            toDelete += lastToDelete.getInstruction().consumeStack(cpgen);
            toDelete -= lastToDelete.getInstruction().produceStack(cpgen);
            if(toDelete == 0) break;
            lastToDelete = lastToDelete.getPrev();
        } while(toDelete > 0);
        try {
            il.delete(lastToDelete, starter);
        } catch(TargetLostException ex){
            for (InstructionHandle target : ex.getTargets()) {
                for (InstructionTargeter t : target.getTargeters()) {
                    if(nextNode == null) throw new RuntimeException("Bad");
                    t.updateTarget(target, nextNode);
                }
            }
        }
    }

    private void optimizeUnusedVariables(InstructionFinder instructionFinder, InstructionList il){
        HashSet<Integer> indices = new HashSet<Integer>();
        Iterator e = instructionFinder.search(Utils.bigStore);
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            indices.add(((StoreInstruction)match[0].getInstruction()).getIndex());
        }
        e = instructionFinder.search(Utils.bigLoad);
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            indices.remove(((LoadInstruction)match[0].getInstruction()).getIndex());
        }
        for(int index : indices) {
            e = instructionFinder.search(Utils.bigStore);
            while(e.hasNext()){
                InstructionHandle[] match = (InstructionHandle[]) e.next();
                if( ((StoreInstruction)match[0].getInstruction()).getIndex() == index){
                    deleteAllStackHandles(match[0], il);
                }
            }
        }
    }

    private abstract class Optimization {
        abstract void run(InstructionFinder instructionFinder, InstructionList il, MethodGen methodGen);
    }

    public void runUntilExhaustion(Optimization optimization, InstructionList il, MethodGen methodGen){
        int ilLength = il.getLength()-1;
        while(il.getLength() != ilLength){
            ilLength = il.getLength();
            InstructionFinder instructionFinder = new InstructionFinder(il);
            optimization.run(instructionFinder, il, methodGen);
            il.setPositions();
        }
    }

	public void optimize()
	{
		gen = new ClassGen(original);
		cpgen = gen.getConstantPool();
		instructionFactory = new InstructionFactory(gen);
        System.out.println(gen.getClassName());

		Method[] methods = gen.getMethods();
		Optimization simpleFolding = new Optimization() {
            @Override
            void run(InstructionFinder instructionFinder, InstructionList il, MethodGen methodGen) {
                simpleFolding(instructionFinder, il);
                removeDeadCode(instructionFinder, il);
            }
        };
        Optimization constantFolding = new Optimization() {
            @Override
            void run(InstructionFinder instructionFinder, InstructionList il, MethodGen methodGen) {
                ArrayList<ConstantVarInfo> constantVarInfos = lookForConstantVariables(instructionFinder, il, methodGen);
                optimizeConstantLoads(instructionFinder, il, constantVarInfos);
            }
        };
        Optimization removeUnusedVariables = new Optimization() {
            @Override
            void run(InstructionFinder instructionFinder, InstructionList il, MethodGen methodGen) {
                optimizeUnusedVariables(instructionFinder, il);
            }
        };
        Optimization simpleConstantFolding = new Optimization() {
            @Override
            void run(InstructionFinder instructionFinder, InstructionList il, MethodGen methodGen) {
                runUntilExhaustion(constantFolding, il, methodGen);
                runUntilExhaustion(removeUnusedVariables, il, methodGen);
                runUntilExhaustion(simpleFolding, il, methodGen);
            }
        };

		for(Method m : methods){
		    System.out.println(m.toString());
            MethodGen methodGen = new MethodGen(m, gen.getClassName(), cpgen);
            InstructionList il = methodGen.getInstructionList();
            if(il == null) continue;
            String unopt = il.toString();

            runUntilExhaustion(simpleFolding, il, methodGen);
            runUntilExhaustion(simpleConstantFolding, il, methodGen);

            String opt = il.toString();
            if(!opt.equals(unopt)){
		        System.out.println(unopt);
		        System.out.println(opt);
            }
            methodGen.setInstructionList(il);
            methodGen.setMaxLocals();
            methodGen.setMaxStack();
            gen.replaceMethod(m, methodGen.getMethod());
        }

        gen.setMajor(50); //Potentially temporary workaround for StackMapTable errors
		this.optimized = gen.getJavaClass();
	}

	
	public void write(String optimisedFilePath)
	{
		this.optimize();

		try {
			FileOutputStream out = new FileOutputStream(new File(optimisedFilePath));
			this.optimized.dump(out);
		} catch (FileNotFoundException e) {
			// Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// Auto-generated catch block
			e.printStackTrace();
		}
	}
}