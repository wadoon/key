package recoder.util;

import java.io.File;
import java.io.FilenameFilter;

public class FileCollector {
    private File[] stack;

    private File current;

    private int count;

    public FileCollector(String root) {
        this(new File(root));
    }

    public FileCollector(File root) {
        this.stack = new File[8];
        this.stack[this.count++] = root;
    }

    private void growStack() {
        File[] newStack = new File[this.stack.length * 2];
        System.arraycopy(this.stack, 0, newStack, 0, this.count);
        this.stack = newStack;
    }

    public boolean next() {
        label21:
        while (this.count > 0) {
            this.current = this.stack[--this.count];
            while (this.current.isDirectory()) {
                String[] content = this.current.list();
                for (int i = content.length - 1; i >= 0; i--) {
                    this.stack[this.count++] = new File(this.current, content[i]);
                    if (this.count == this.stack.length)
                        growStack();
                }
                if (this.count == 0)
                    break label21;
                this.current = this.stack[--this.count];
            }
            if (this.current.exists())
                return true;
        }
        this.current = null;
        return false;
    }

    public boolean next(String suffix) {
        while (next()) {
            if (this.current.getName().endsWith(suffix))
                return true;
        }
        return false;
    }

    public boolean next(FilenameFilter filter) {
        String pname = "";
        File pfile = null;
        while (next()) {
            String p = this.current.getParent();
            if (p == null)
                p = "";
            if (!pname.equals(p)) {
                pname = p;
                pfile = new File(pname);
            }
            if (filter.accept(pfile, this.current.getName()))
                return true;
        }
        return false;
    }

    public File getFile() {
        return this.current;
    }
}
