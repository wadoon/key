package de.uka.ilkd.key.proof.io;

/**
 * This factory creates problem loaders but also disposes an obtained proof
 * before throwing an exception. Those proof disposals seem unnecessary but I
 * did not introduce them so who knows what they are good for...
 * 
 * @author Kai Wallisch
 *
 */
public abstract class SingleThreadProblemLoaderFactory<T extends AbstractProblemLoader> {

    protected abstract T createProblemLoader() throws ProblemLoaderException;

    public T load() throws ProblemLoaderException {

        T loader = null;
        try {
            loader = createProblemLoader();
            loader.load();
            return loader;
        } catch (Throwable e) {
            if (loader != null && loader.getProof() != null) {
                loader.getProof().dispose();
            }
            // rethrow that exception
            if (e instanceof ProblemLoaderException) {
                throw (ProblemLoaderException) e;
            } else {
                throw new ProblemLoaderException(loader, e);
            }
        }
    }

}
