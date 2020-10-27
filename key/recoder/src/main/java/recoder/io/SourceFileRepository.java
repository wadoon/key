package recoder.io;

import recoder.ParserException;
import recoder.Service;
import recoder.java.CompilationUnit;
import recoder.util.ProgressListener;

import java.io.FilenameFilter;
import java.io.IOException;
import java.util.List;

public interface SourceFileRepository extends Service {
    List<CompilationUnit> getCompilationUnits();

    List<CompilationUnit> getKnownCompilationUnits();

    DataLocation findSourceFile(String paramString);

    CompilationUnit getCompilationUnit(String paramString);

    CompilationUnit getCompilationUnitFromFile(String paramString) throws ParserException;

    List<CompilationUnit> getCompilationUnitsFromFiles(String[] paramArrayOfString) throws ParserException;

    List<CompilationUnit> getAllCompilationUnitsFromPath() throws ParserException;

    List<CompilationUnit> getAllCompilationUnitsFromPath(FilenameFilter paramFilenameFilter) throws ParserException;

    boolean isUpToDate(CompilationUnit paramCompilationUnit);

    void print(CompilationUnit paramCompilationUnit) throws IOException;

    void printAll(boolean paramBoolean) throws IOException;

    void cleanUp();

    void addProgressListener(ProgressListener paramProgressListener);

    void removeProgressListener(ProgressListener paramProgressListener);
}
