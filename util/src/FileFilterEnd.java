package warwick.marsh.util;

import java.io.File;
import javax.swing.filechooser.FileFilter;

/**
 * File filter to select files of the form *end where
 * end is supplied to the constructor.
 */
public class FileFilterEnd extends FileFilter {
    
    private String end = null;

    public FileFilterEnd(String end){
	super();
	this.end = end;
    }

    public boolean accept(File file) {
	return (file.isDirectory() || file.getName().endsWith(end));
    }
    
    public String getDescription(){
	return end;
    }
    
}
