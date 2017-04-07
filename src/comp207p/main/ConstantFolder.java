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

    public static class Utils {
        private final static Type[] arithmeticTypes = {Type.BYTE, Type.INT, Type.LONG, Type.FLOAT, Type.DOUBLE, Type.SHORT, Type.CHAR};
        private final static Type[] integralTypes = {Type.BYTE, Type.INT, Type.LONG, Type.SHORT, Type.CHAR};
        private final static Class[] addInstructions = {IADD.class, DADD.class, FADD.class, LADD.class};
        private final static Class[] subInstructions = {ISUB.class, DSUB.class, FSUB.class, LSUB.class};
        private final static Class[] mulInstructions = {IMUL.class, DMUL.class, FMUL.class, LMUL.class};
        private final static Class[] divInstructions = {IDIV.class, DDIV.class, FDIV.class, LDIV.class};
        private final static Class[] remInstructions = {IREM.class, DREM.class, FREM.class ,LREM.class};
        private final static Class[] negInstructions = {INEG.class, DNEG.class, FNEG.class, LNEG.class};
        private final static Class[] orInstructions = {IOR.class, LOR.class};
        private final static Class[] xorInstructions = {IXOR.class, LXOR.class};
        private final static Class[] andInstructions = {IAND.class, LAND.class};
        private final static Class[] shlInstructions = {ISHL.class, LSHL.class};
        private final static Class[] shrInstructions = {ISHR.class, LSHR.class};
        private final static Class[] ushrInstructions = {IUSHR.class, LUSHR.class};
        //public final static String bigStore = "(StoreInstruction|lstore_0|lstore_1|lstore_2|lstore_3|fstore_0|fstore_1|fstore_2|fstore_3|astore_0|astore_1|astore_2|astore_3|dstore_0|dstore_1|dstore_2|dstore_3)";
        //public final static String bigLoad = "(LoadInstruction|lload_0|lload_1|lload_2|lload_3|fload_0|fload_1|fload_2|fload_3|aload_0|aload_1|aload_2|aload_3|dload_0|dload_1|dload_2|dload_3)";
        public final static String bigStore = "(StoreInstruction)";
        public final static String bigLoad = "(LoadInstruction)";
        public final static String bigCmp = "(LCMP|DCMPL|DCMPG|FCMPG|FCMPL)";


        private static boolean isType(Type t, Type[] set) {
            for (Type t2 : set) {
                if (t.equals(t2)) return true;
            }
            return false;
        }

        public static boolean isArithmeticType(Type t) {
            return isType(t, arithmeticTypes);
        }
        public static boolean isIntegralType(Type t){
            return isType(t, integralTypes);
        }

        private static boolean isInstruction(Instruction instruction, Class[] classes){
            for(Class c : classes){
                if(instruction.getClass().equals(c)) return true;
            }
            return false;
        }
        private static String instructionList(Class[] instructions){
            String res = "(";
            for(Class c : instructions){
                res += c.getName()+"|";
            }
            return res.substring(0,res.length()-1)+")";
        }

        public static Type getPushType(Instruction instruction, ConstantPoolGen cpgen){
            if(instruction instanceof LDC){
                return ((LDC)instruction).getType(cpgen);
            }
            if(instruction instanceof LDC2_W){
                return ((LDC2_W)instruction).getType(cpgen);
            }
            if(instruction instanceof ConstantPushInstruction){
                return ((ConstantPushInstruction)instruction).getType(cpgen);
            }
            return null;
        }

        public static Number getPushValue(Instruction instruction, ConstantPoolGen cpgen){
            if(instruction instanceof LDC || instruction instanceof LDC2_W){
                Object value;
                value = instruction instanceof LDC ? ((LDC)instruction).getValue(cpgen) : ((LDC2_W)instruction).getValue(cpgen);
                if(value instanceof Number)
                    return (Number)value;
                else
                    return null;
            }
            if(instruction instanceof ConstantPushInstruction){
                return ((ConstantPushInstruction)instruction).getValue();
            }
            return null;
        }

        public static Object downgradeLong(Long n){
            if(n >= Byte.MIN_VALUE && n <= Byte.MAX_VALUE) return n.byteValue();
            if(n >= Short.MIN_VALUE && n <= Short.MAX_VALUE) return n.shortValue();
            if(n >= Integer.MIN_VALUE && n <= Integer.MAX_VALUE) return n.intValue();
            else return n;
        }

        public static boolean computeIfResult(Object value1, Object value2, IfInstruction instruction, ConstantPoolGen cpgen){
            if(instruction instanceof IFEQ) return ((Number)value2).intValue() == 0;
            if(instruction instanceof IFGE) return ((Number)value2).intValue() >= 0;
            if(instruction instanceof IFGT) return ((Number)value2).intValue() > 0;
            if(instruction instanceof IFLE) return ((Number)value2).intValue() <= 0;
            if(instruction instanceof IFLT) return ((Number)value2).intValue() < 0;
            if(instruction instanceof IFNE) return ((Number)value2).intValue() != 0;
            //if(instruction instanceof IFNONNULL) return value2 != null;
            //if(instruction instanceof IFNULL) return value2 == null;
            //if(instruction instanceof IF_ACMPEQ) return value1 == value2;
            //if(instruction instanceof IF_ACMPNEQ) return value1 != value2;
            if(instruction instanceof IF_ICMPEQ) return ((Number)value1).intValue() == ((Number)value2).intValue();
            if(instruction instanceof IF_ICMPGE) return ((Number)value1).intValue() >= ((Number)value2).intValue();
            if(instruction instanceof IF_ICMPGT) return ((Number)value1).intValue() > ((Number)value2).intValue();
            if(instruction instanceof IF_ICMPLE) return ((Number)value1).intValue() <= ((Number)value2).intValue();
            if(instruction instanceof IF_ICMPLT) return ((Number)value1).intValue() < ((Number)value2).intValue();
            if(instruction instanceof IF_ICMPNE) return ((Number)value1).intValue() != ((Number)value2).intValue();
            throw new RuntimeException("Non-exhaustive if cases");
        }

        public static int computeCmpResult(Number value1, Number value2, Instruction instruction){
            if(instruction instanceof LCMP) return value1.longValue() == value2.longValue() ? 0 : (value1.longValue() > value2.longValue() ? 1 : -1);
            if(instruction instanceof DCMPG) return value1.doubleValue() > value2.doubleValue() ? 1 : 0;
            if(instruction instanceof DCMPL) return value1.doubleValue() < value2.doubleValue() ? 1 : 0;
            if(instruction instanceof FCMPG) return value1.floatValue() > value2.floatValue() ? 1 : 0;
            if(instruction instanceof FCMPL) return value1.floatValue() < value2.floatValue() ? 1 : 0;
            throw new RuntimeException("Non-exhaustive if cases");
        }

        public static Object computeBinaryResult(Number value1, Number value2, ArithmeticInstruction instruction, ConstantPoolGen cpgen){
            Type resultType = instruction.getType(cpgen);
            if(resultType.equals(Type.INT)){
                Integer val1 = (Integer)value1;
                Integer val2 = (Integer)value2;
                if(isInstruction(instruction, addInstructions))
                    return val1 + val2;
                if(isInstruction(instruction, subInstructions))
                    return val1 - val2;
                if(isInstruction(instruction, mulInstructions))
                    return val1 * val2;
                if(isInstruction(instruction, divInstructions))
                    return val1 / val2;
                if(isInstruction(instruction, remInstructions))
                    return val1 % val2;
                if(isInstruction(instruction, negInstructions))
                    return -val2;
                if(isInstruction(instruction, orInstructions))
                    return val1 | val2;
                if(isInstruction(instruction, xorInstructions))
                    return val1 ^ val2;
                if(isInstruction(instruction, andInstructions))
                    return val1 & val2;
                if(isInstruction(instruction, shlInstructions))
                    return val1 << val2;
                if(isInstruction(instruction, shrInstructions))
                    return val1 >> val2;
                if(isInstruction(instruction, ushrInstructions))
                    return val1 >>> val2;
            }
            if(resultType.equals(Type.LONG)){
                Long val1 = (Long)value1;
                Long val2 = (Long)value2;
                if(isInstruction(instruction, addInstructions))
                    return val1 + val2;
                if(isInstruction(instruction, subInstructions))
                    return val1 - val2;
                if(isInstruction(instruction, mulInstructions))
                    return val1 * val2;
                if(isInstruction(instruction, divInstructions))
                    return val1 / val2;
                if(isInstruction(instruction, remInstructions))
                    return val1 % val2;
                if(isInstruction(instruction, negInstructions))
                    return -val2;
                if(isInstruction(instruction, orInstructions))
                    return val1 | val2;
                if(isInstruction(instruction, xorInstructions))
                    return val1 ^ val2;
                if(isInstruction(instruction, andInstructions))
                    return val1 & val2;
                if(isInstruction(instruction, shlInstructions))
                    return val1 << val2;
                if(isInstruction(instruction, shrInstructions))
                    return val1 >> val2;
                if(isInstruction(instruction, ushrInstructions))
                    return val1 >>> val2;
            }
            if(resultType.equals(Type.DOUBLE)){
                Double val1 = (Double)value1;
                Double val2 = (Double)value2;
                if(isInstruction(instruction, addInstructions))
                    return val1 + val2;
                if(isInstruction(instruction, subInstructions))
                    return val1 - val2;
                if(isInstruction(instruction, mulInstructions))
                    return val1 * val2;
                if(isInstruction(instruction, divInstructions))
                    return val1 / val2;
                if(isInstruction(instruction, remInstructions))
                    return val1 % val2;
                if(isInstruction(instruction, negInstructions))
                    return -val2;
            }
            if(resultType.equals(Type.FLOAT)){
                Float val1 = (Float)value1;
                Float val2 = (Float)value2;
                if(isInstruction(instruction, addInstructions))
                    return val1 + val2;
                if(isInstruction(instruction, subInstructions))
                    return val1 - val2;
                if(isInstruction(instruction, mulInstructions))
                    return val1 * val2;
                if(isInstruction(instruction, divInstructions))
                    return val1 / val2;
                if(isInstruction(instruction, remInstructions))
                    return val1 % val2;
                if(isInstruction(instruction, negInstructions))
                    return -val2;
            }

            return null;
        }

        public static Class TypeToJavaClass(Type t){
            if(t.equals(Type.BYTE)) return Byte.class;
            if(t.equals(Type.FLOAT)) return Float.class;
            if(t.equals(Type.LONG)) return Long.class;
            if(t.equals(Type.INT)) return Integer.class;
            if(t.equals(Type.BOOLEAN)) return Boolean.class;
            if(t.equals(Type.CHAR)) return Character.class;
            if(t.equals(Type.CLASS)) return Class.class;
            if(t.equals(Type.DOUBLE)) return Double.class;
            return null;
        }

        public static Object convertObject(Type resultType, Number toCast) {
            Object result = null;
            if (resultType == Type.BYTE) {
                result = toCast.byteValue();
            }
            if (resultType == Type.BOOLEAN) {
                result = toCast.intValue() == 0 ? 0 : 1;
            }
            if (resultType == Type.CHAR) {
                result = (char) toCast.byteValue();
            }
            if (resultType == Type.DOUBLE) {
                result = toCast.doubleValue();
            }
            if (resultType == Type.FLOAT) {
                result = toCast.floatValue();
            }
            if (resultType == Type.INT) {
                result = toCast.intValue();
            }
            if (resultType == Type.LONG) {
                result = toCast.longValue();
            }
            if (resultType == Type.SHORT) {
                result = toCast.shortValue();
            }
            return result;
        }
    }


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
        public boolean finalisedValidPos = false;
    }

    private int constantVarInfosAdd(ArrayList<ConstantVarInfo> constantVarInfos, ConstantVarInfo toAdd){
        ArrayList<ConstantVarInfo> toDeleteList = new ArrayList<>();
        boolean canBeAdded = true;
        for(ConstantVarInfo i : constantVarInfos){
            if(i.index != toAdd.index) continue;
            if(toAdd.assignPosition == i.assignPosition && i.lastValidPosition >= toAdd.assignPosition){
                if(toAdd.value == i.value){ //Combine
                    //i.lastValidPosition = Math.max(toAdd.lastValidPosition, i.lastValidPosition);
                    return 0;
                }
                else if(i.finalisedValidPos){ //Conflict
                    toDeleteList.add(i);
                    canBeAdded = false;
                }
            }
            else if(i.assignPosition == toAdd.assignPosition && toAdd.lastValidPosition >= i.assignPosition){
                if(toAdd.value == i.value){ //Combine
                    if(i.assignPosition > toAdd.assignPosition) {
                        i.assignPosition = toAdd.assignPosition;
                        return 1;
                    }
                    return 0;
                }
                else if(i.finalisedValidPos){ //Conflict
                    toDeleteList.add(i);
                    canBeAdded = false;
                }
            }
        }
        constantVarInfos.removeAll(toDeleteList);
        if(!toDeleteList.isEmpty()) return 1;
        if(canBeAdded){
            constantVarInfos.add(toAdd);
            return 1;
        }
        return 0;
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
            info.lastValidPosition = il.getEnd().getPosition(); info.finalisedValidPos = false;
            constantVarInfos.add(info);
        }

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
                info.lastValidPosition = nearestInstruction.getPosition(); info.finalisedValidPos = true;
                if(nearestInstruction.getInstruction() instanceof BranchInstruction){
                    BranchInstruction branchInstruction = ((BranchInstruction)nearestInstruction.getInstruction());
                    ConstantVarInfo i = new ConstantVarInfo();
                    i.assignPosition = branchInstruction.getTarget().getPosition();
                    i.lastValidPosition = il.getEnd().getPosition(); i.finalisedValidPos = false;
                    i.index = info.index;
                    i.value = info.value;
                    toAdd.add(i);
                    if(nearestInstruction.getInstruction() instanceof IfInstruction && nearestInstruction.getNext() != null){
                        ConstantVarInfo i2 = new ConstantVarInfo();
                        i2.assignPosition = nearestInstruction.getNext().getPosition();
                        i2.lastValidPosition = il.getEnd().getPosition(); i.finalisedValidPos = false;
                        i2.index = info.index;
                        i2.value = info.value;
                        toAdd.add(i2);
                    }
                }
            }
            int numAdded = 0;
            for(ConstantVarInfo i : toAdd) {
                numAdded += constantVarInfosAdd(constantVarInfos, i);
            }
            if(numAdded == 0) toAdd.clear();
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
                if(info.assignPosition > instruction.getTarget().getPosition()) continue;
                if(info.lastValidPosition >= instruction.getTarget().getPosition()){
                    Iterator e2 = instructionFinder.search(Utils.bigStore+"|IINC|BranchInstruction", instruction.getTarget());
                    boolean modifiedVariable = false;
                    while(e2.hasNext()){
                        InstructionHandle[] match2 = (InstructionHandle[]) e2.next();
                        int index = -1;
                        if(match2[0].getInstruction() instanceof StoreInstruction) index = ((StoreInstruction) match2[0].getInstruction()).getIndex();
                        if(match2[0].getInstruction() instanceof IINC) index = ((IINC) match2[0].getInstruction()).getIndex();
                        if(match2[0].getInstruction() instanceof BranchInstruction) {
                            if(((BranchInstruction)match2[0].getInstruction()).getTarget().getPosition() >= instruction.getTarget().getPosition()) continue;
                            else modifiedVariable = true;
                        }
                        if(index != info.index) continue;
                        if(instruction.getTarget().getPosition() < match[0].getPosition()) { //Back jump
                            if (match2[0].getPosition() > match[0].getPosition()) continue;
                        }
                        modifiedVariable = true;
                    }
                    if(!modifiedVariable) continue;
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
        Iterator e = instructionFinder.search(Utils.bigStore);
        while(e.hasNext()){
            InstructionHandle[] match = (InstructionHandle[]) e.next();
            StoreInstruction storeInstruction = (StoreInstruction) match[0].getInstruction();
            Iterator e2 = instructionFinder.search(Utils.bigLoad + "|BranchInstruction", match[0]);
            boolean isUselessStore = true;
            while(e2.hasNext()){
                InstructionHandle[] match2 = (InstructionHandle[]) e2.next();
                if(match2[0].getInstruction() instanceof LoadInstruction){
                    if(((LoadInstruction)match2[0].getInstruction()).getIndex() == storeInstruction.getIndex()){
                        isUselessStore = false;
                        break;
                    }
                }
                if(match2[0].getInstruction() instanceof BranchInstruction){
                    if(((BranchInstruction)match2[0].getInstruction()).getTarget().getPosition() > match[0].getPosition()) continue;
                    isUselessStore = false; //This could be improved
                    break;
                }
            }
            if(isUselessStore){
                deleteAllStackHandles(match[0], il);
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

		Method[] methods = gen.getMethods();
		Optimization removeDeadCode = new Optimization() {
            @Override
            void run(InstructionFinder instructionFinder, InstructionList il, MethodGen methodGen) {
                removeDeadCode(instructionFinder, il);
            }
        };
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
                runUntilExhaustion(removeDeadCode, il, methodGen);
            }
        };

		for(Method m : methods){
            MethodGen methodGen = new MethodGen(m, gen.getClassName(), cpgen);
            InstructionList il = methodGen.getInstructionList();
            if(il == null) continue;

            runUntilExhaustion(simpleFolding, il, methodGen);
            runUntilExhaustion(simpleConstantFolding, il, methodGen);

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