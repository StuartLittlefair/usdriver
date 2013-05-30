package warwick.marsh.util;

import java.io.File;
import javax.swing.filechooser.FileFilter;

/**
 * File filter to select files of the form *.dat
 * 
 */
public class FileFilterDat extends FileFilter {
    
    public boolean accept(File file) {
	return (file.isDirectory() || file.getName().endsWith(".dat"));
    }
    
    public String getDescription(){
	return "*.dat";
    }
    
}
