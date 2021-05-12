import java.util.*;

class FunctionProofObligations {
    public String onlyIf;
    public String assumes;
    public String onSuccess;
    public List<String> assignable = new LinkedList<>();
    public boolean isGross;

    public void addOnlyIf(String s) {
        onlyIf = onlyIf == null ? s : onlyIf + " & " + s;
    }

    public void addAssumes(String s) {
        assumes = assumes == null ? s : assumes + " & " + s;
    }

    public void addOnSuccess(String s) {
        onSuccess = onSuccess == null ? s : onSuccess + " & " + s;
    }

    public void addAssignable(String s) {
        assignable.add(s);
    }

    public void setGross(boolean g) {
        isGross = g;
    }

    public boolean isGross() {
        return isGross;
    }
}

