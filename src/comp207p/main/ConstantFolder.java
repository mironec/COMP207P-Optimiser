package comp207p.main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

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

    public void simpleFolding(InstructionFinder instructionFinder, InstructionList il){
        Iterator e = instructionFinder.search("(ConstantPushInstruction|LDC)(ConstantPushInstruction|LDC)(ArithmeticInstruction)");
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            Type instType1, instType2;
            instType1 = Utils.getPushType(match[0].getInstruction(), cpgen);
            instType2 = Utils.getPushType(match[1].getInstruction(), cpgen);
            if(! (Utils.isArithmeticType(instType1) && Utils.isArithmeticType(instType2))){
                System.err.println("THAT'S REALLY WEIRD.");
                continue;
            }
            Object constant = Utils.computeBinaryResult(Utils.getPushValue(match[0].getInstruction(), cpgen),
                    Utils.getPushValue(match[1].getInstruction(), cpgen),
                    (ArithmeticInstruction) match[2].getInstruction(), cpgen);
            try {
                il.delete(match[0], match[1]);
            } catch(TargetLostException ex){
                for (InstructionHandle target : ex.getTargets()) {
                    for (InstructionTargeter t : target.getTargeters()) {
                        t.updateTarget(target, match[2]);
                    }
                }
            }
            match[2].setInstruction(instructionFactory.createConstant(constant));
        }
        e = instructionFinder.search("(ConstantPushInstruction|LDC)(INEG|LNEG|FNEG|DNEG)");
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
    }

    private class ConstantVarInfo {
        public Object value;
        public int index;
        public int assignPosition;
        public int lastValidPosition;
    }

    private ArrayList<ConstantVarInfo> lookForConstantVariables(InstructionFinder instructionFinder, InstructionList il, MethodGen m) {
        Iterator e = instructionFinder.search("(ConstantPushInstruction|LDC)(StoreInstruction)");
        ArrayList<ConstantVarInfo> constantVarInfos = new ArrayList<>();
        while (e.hasNext()) {
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            ConstantVarInfo info = new ConstantVarInfo();
            if (match[0].getInstruction() instanceof ConstantPushInstruction)
                info.value = ((ConstantPushInstruction) match[0].getInstruction()).getValue();
            else
                info.value = ((LDC) match[0].getInstruction()).getValue(cpgen);
            info.assignPosition = match[1].getPosition();
            info.index = ((StoreInstruction) match[1].getInstruction()).getIndex();
            info.lastValidPosition = il.getEnd().getPosition();
            constantVarInfos.add(info);
        }
        for(ConstantVarInfo i : constantVarInfos) {
            for (ConstantVarInfo i2 : constantVarInfos) {
                if (i2.index == i.index && i2.lastValidPosition > i.assignPosition && i.assignPosition > i2.assignPosition) {
                    i2.lastValidPosition = i.assignPosition;
                }
            }
        }

        e = instructionFinder.search("StoreInstruction");
        while (e.hasNext()) {
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            StoreInstruction instruction = (StoreInstruction) match[0].getInstruction();
            for(ConstantVarInfo i : constantVarInfos) {
                if (i.index == instruction.getIndex() && i.lastValidPosition > match[0].getPosition() && match[0].getPosition() > i.assignPosition) {
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
                if(info.lastValidPosition >= instruction.getTarget().getPosition()){
                    info.lastValidPosition = instruction.getTarget().getPosition()-1;
                }
            }
        }

        return constantVarInfos;
    }

    private void optimizeConstantLoads(InstructionFinder instructionFinder, InstructionList il, ArrayList<ConstantVarInfo> constantVarInfos){
        Iterator e = instructionFinder.search("LoadInstruction");
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

    private void optimizeUnusedVariables(InstructionFinder instructionFinder, InstructionList il){
        HashSet<Integer> indices = new HashSet<Integer>();
        Iterator e = instructionFinder.search("StoreInstruction");
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            indices.add(((StoreInstruction)match[0].getInstruction()).getIndex());
        }
        e = instructionFinder.search("LoadInstruction");
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            indices.remove(((LoadInstruction)match[0].getInstruction()).getIndex());
        }
        for(int index : indices) {
            e = instructionFinder.search("StoreInstruction");
            while(e.hasNext()){
                InstructionHandle[] match = (InstructionHandle[]) e.next();
                if( ((StoreInstruction)match[0].getInstruction()).getIndex() == index){
                    InstructionHandle nextNode = match[0].getNext();
                    try {
                        if(match[0].getPrev() == null) throw new RuntimeException("This should never happen");
                        il.delete(match[0].getPrev(), match[0]);
                    } catch(TargetLostException ex){
                        for (InstructionHandle target : ex.getTargets()) {
                            for (InstructionTargeter t : target.getTargeters()) {
                                if(nextNode == null) throw new RuntimeException("Bad");
                                t.updateTarget(target, nextNode);
                            }
                        }
                    }
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