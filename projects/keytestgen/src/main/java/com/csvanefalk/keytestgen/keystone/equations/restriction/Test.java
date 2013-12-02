package com.csvanefalk.keytestgen.keystone.equations.restriction;

import com.csvanefalk.keytestgen.keystone.equations.IExpression;
import com.csvanefalk.keytestgen.keystone.equations.expression.Addition;
import com.csvanefalk.keytestgen.keystone.equations.expression.NumericConstant;
import org.apache.commons.math3.fraction.Fraction;

import java.util.Calendar;

public class Test {

    public static void main(final String[] args) {

        final long millis = Calendar.getInstance().getTimeInMillis();
        final int batch = 8000 * 1000;

        final IExpression[] strings = new IExpression[batch];
        final long start = System.nanoTime();

        for (int j = 0; j < batch; j++) {
            strings[j] = new Addition(new NumericConstant(new Fraction(j)),
                    new NumericConstant(new Fraction(j)));
        }

        final long time = System.nanoTime() - start;
        System.out.printf("Average object allocation took %.1f ns.%n",
                (double) time / batch);

        System.out.println(Calendar.getInstance().getTimeInMillis() - millis);
    }
}
