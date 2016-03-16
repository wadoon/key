package de.uka.ilkd.key.nui.exceptions;

import de.uka.ilkd.key.nui.controller.TreeViewController;

/**
 * Exception thrown by {@link TreeViewController#openSearchView()} if the
 * searchView was never added before, see
 * {@link TreeViewController#addSearchView(SearchPane, SearchViewController)}.
 * 
 * @author Florian Breitfelder
 *
 */
public class NoSearchViewAddedException extends NUIException {

    private static final long serialVersionUID = 1L;

    @Override
    public String getMessage() {
        return "No searchView was added before.";

    }

}
