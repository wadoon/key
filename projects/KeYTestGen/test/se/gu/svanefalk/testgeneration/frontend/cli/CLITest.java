package se.gu.svanefalk.testgeneration.frontend.cli;

import java.util.LinkedList;
import java.util.List;

public class CLITest {

    protected List<String> getList(String... strings) {

        List<String> stringList = new LinkedList<>();
        for (String string : strings) {
            stringList.add(string);
        }

        return stringList;
    }

    protected <T> boolean assertListEquality(List<T> firstList,
            List<T> secondList) {

        boolean passedLoop = false;
        for (T firstObject : firstList) {
            for (T secondObject : secondList) {
                if (firstObject.equals(secondObject)) {
                    secondList.remove(secondObject);
                    passedLoop = true;
                    break;
                }
            }
            if (!passedLoop) {
                return false;
            } else {
                passedLoop = false;
            }
        }

        return true;
    }
}
