package comp207p.main;

import org.apache.bcel.generic.*;

/**
 * Created by Miron on 19/03/2017.
 */
public class Utils {
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
