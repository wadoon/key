package se.gu.svanefalk.testgeneration;

import org.junit.Test;

public class TestSMTParsing extends KeYTestGenTest {

    private final String output = "(define-fun self_dot_instanceY_3 () Int    (- 1434))  "
            + "(define-fun self_dot_instanceZ_6 () Int    1234)  "
            + "(define-fun self_dot_instanceZ_2 () Int    0)  "
            + "(define-fun self_dot_instanceY_4 () Int    0)  "
            + "(define-fun x_5 () Int    0))\n";

    @Test
    public void test() {

        final String[] definitions = output.split("\\(define-fun");

        for (String definition : definitions) {

            if (!definition.isEmpty()) {

                definition = definition.trim();

                definition.substring(0, definition.lastIndexOf('_'));

                boolean negFlag = false;
                for (int i = definition.indexOf(' '); i < definition.length(); i++) {

                    final char currentChar = definition.charAt(i);

                    if (!negFlag && (currentChar == '-')) {
                        negFlag = true;
                    }

                    if (Character.isDigit(currentChar)) {
                    }
                }
            }
        }
    }
}