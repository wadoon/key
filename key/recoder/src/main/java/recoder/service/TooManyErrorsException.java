/**
 *
 */
package recoder.service;

import recoder.ModelException;

import java.util.Collections;
import java.util.List;

/**
 * @author Tobias
 *
 */
public class TooManyErrorsException extends ModelException {
    private final List<Exception> errors;

    public TooManyErrorsException(String s, List<Exception> errors) {
        super(s);
        this.errors = Collections.unmodifiableList(errors);
    }

    public List<Exception> getErrors() {
        return errors;
    }
}
