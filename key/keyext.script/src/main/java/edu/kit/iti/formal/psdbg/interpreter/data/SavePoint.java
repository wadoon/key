package edu.kit.iti.formal.psdbg.interpreter.data;

import edu.kit.iti.formal.psdbg.parser.DefaultASTVisitor;
import edu.kit.iti.formal.psdbg.parser.ast.*;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.Getter;
import lombok.RequiredArgsConstructor;

import java.io.File;

@Data
@RequiredArgsConstructor
@AllArgsConstructor
public class SavePoint {
    @Getter
    private final String name;
    private int startOffset = -1;
    private int endOffset = -1;
    @Getter
    private int lineNumber = -1;
    private ForceOption force = ForceOption.YES;

    public SavePoint(CallStatement call) {
        if (isSaveCommand(call)) {
            Parameters p = call.getParameters();
            name = evalAsText(p, "#2", "not-available");
            try{
                force = ForceOption.valueOf(evalAsText(p, "force", "yes").toUpperCase());
            } catch (IllegalArgumentException e){

            }

            try {
                startOffset = call.getRuleContext().getStart().getStartIndex();
                endOffset = call.getRuleContext().getStart().getStopIndex();
                lineNumber = call.getRuleContext().getStart().getLine();
            } catch (NullPointerException npe) {
            }
        } else {
            throw new IllegalArgumentException(call.getCommand() + " is not a save statement");
        }
    }

    public static boolean isSaveCommand(CallStatement call) {
        return (call.getCommand().equals("#save"));
    }

    public static boolean isSaveCommand(Statement statement) {
        try {
            CallStatement c = (CallStatement) statement;
            return isSaveCommand(c);
        } catch (ClassCastException e) {
            return false;
        }
    }

    public boolean exists(File dir) {
        return getProofFile(dir).exists() && getPersistedStateFile(dir).exists();
    }

    public static String evalAsText(Parameters p, String key, String defaultValue) {
        Variable k = new Variable(key);
        if (!p.containsKey(k)) {
            return defaultValue;
        }

        return (String) p.get(k).accept(new DefaultASTVisitor<String>() {
            @Override
            public String defaultVisit(ASTNode node) {
                throw new IllegalArgumentException();
            }

            @Override
            public String visit(Variable variable) {
                return variable.getIdentifier();
            }

            @Override
            public String visit(StringLiteral stringLiteral) {
                return stringLiteral.getText();
            }

            @Override
            public String visit(BooleanLiteral booleanLiteral) {
                return Boolean.toString(booleanLiteral.isValue());
            }

            @Override
            public String visit(IntegerLiteral integer) {
                return (integer.getValue().toString());
            }
        });
    }

    public File getProofFile(File dir) {
        return new File(dir, name + ".proof");
    }

    public File getPersistedStateFile(File dir) {
        return new File(dir, name + ".psdbgstate.xml");
    }

    public boolean isThisStatement(Statement statement) {
        if (isSaveCommand(statement)) {
            CallStatement c = (CallStatement) statement;
            return c.getCommand().equals(name);

        }
        return false;
    }

    public enum ForceOption {
        YES, NO, INTERACTIVE;
    }
}
