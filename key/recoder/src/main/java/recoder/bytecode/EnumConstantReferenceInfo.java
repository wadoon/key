package recoder.bytecode;

public class EnumConstantReferenceInfo {
    private final String typeName;

    private final String constName;

    public EnumConstantReferenceInfo(String typeName, String constName) {
        this.typeName = typeName;
        this.constName = constName;
    }

    public String getTypeName() {
        return this.typeName;
    }

    public String getConstName() {
        return this.constName;
    }
}
