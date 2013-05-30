
package warwick.marsh.ultracam;

import java.io.File;
import java.io.FileWriter;

import javax.swing.*;
import javax.swing.border.LineBorder;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;
import java.awt.Color;
import java.awt.BorderLayout;
import java.awt.GridLayout;
import java.awt.Dimension;

import java.util.Date;
import java.text.DateFormat;

import org.w3c.dom.Comment;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Text;

import warwick.marsh.util.*;

/**
 * Class for logging in Udriver both to a JTextPane and a file if wanted.
 *
 */

public class LogPanel extends JPanel {

    public static final int OK      = 1;
    public static final int WARNING = 2;
    public static final int ERROR   = 3;

    // Maximum size to prevent the scrollable area eating up 
    // rest of GUI.
    static final int MAX_X_SIZE = 400;
    static final int MAX_Y_SIZE = 100;

    // Maximum number of rows to display to make it easier to scroll back
    // This is basically a 'history' limit
    static final int MAX_ROW = 100;

    // These are used to define the start and end of rows
    static final String START_ROW = "<tr valign=\"top\">";
    static final String END_ROW   = "</tr>\n";

    private StringBuffer _htmlBuffer     = new StringBuffer();

    private boolean      _logEnabled     = false;
    private File         _logFile        = null;
    private FileWriter   _logFileWriter  = null;
    private JFileChooser _logFileChooser = null;
    private JTextPane    _pane           = new JTextPane();

    public LogPanel(String LOG_FILE_DIRECTORY) {

	super(new GridLayout(1,1));

	// Set up pane
	_pane.setEditable(false);
	_pane.setContentType("text/html");
	_pane.setMaximumSize(new Dimension(MAX_X_SIZE, MAX_Y_SIZE));
	
	JScrollPane scrollPane = new JScrollPane(_pane, JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
	add(scrollPane);

	_logFileChooser = new JFileChooser();
	_logFileChooser.setFileFilter(new FileFilterHTML());
	_logFileChooser.setCurrentDirectory(new File(LOG_FILE_DIRECTORY));

	setPreferredSize(new Dimension(MAX_X_SIZE, MAX_Y_SIZE));
	setMaximumSize(new Dimension(MAX_X_SIZE, MAX_Y_SIZE));
    }
    
    /** This adds a row to the log in html format 
     * @param text   text to add. Will be wrapped up in an html table row.
     * @param type   OK, WARNING or ERROR to indicate colour. 
     * @param fileTo true to send the line to the log file (if logging enabled) as well as screen
     * There could well be cases where it was not of interest to keep a written record (e.g. of many
     * of the error messages).
     */
    public void add(String text, int type, boolean fileToo) {

	
	Date       date = new Date();
	DateFormat df   = DateFormat.getTimeInstance(DateFormat.MEDIUM);

	// Add the row into the internal buffer
	_htmlBuffer.append(START_ROW + 
			   "<td width=\"80\">" + df.format(date) + "</td> <td" + _bgcolor(type) + ">" + text + "</td>" +
			   END_ROW);

	// Limit the number of rows
	limitRows();

	_pane.setText("<table>\n" + _htmlBuffer.toString() + "</table>\n");

	// now optionally to a file
	if(_logEnabled && fileToo){

	    try {
		
		_logFileWriter.write(START_ROW + 
				     "<td width=\"80\">" + df.format(date) + "</td> <td" + _bgcolor(type) + ">" + text + "</td>" +
				     END_ROW);
		
	    }
	    catch(Exception e){
		_close();
		add(e.toString() + ". File logging disabled.", ERROR, false);
	    }
	}
    }

    public void startLog(){

	try{

	    if(!_logEnabled){
		int result = _logFileChooser.showDialog(null, "Log file");
		if(result == JFileChooser.APPROVE_OPTION){
		    _logFile = _logFileChooser.getSelectedFile();
		    if (_logFile.getPath().indexOf(".html") != _logFile.getPath().length() - 5 ){
			String newFilePath = _logFile.getPath() + ".html";
			_logFile = new File(newFilePath);
		    }
		    
		    Date       date = new Date();
		    DateFormat df   = DateFormat.getDateTimeInstance(DateFormat.MEDIUM, DateFormat.MEDIUM);
		    
		    // Write, appending to end
		    if(_logFile.exists()){
			add("Will append to <strong>" + _logFile.getName() + "</strong>", OK, false);
			_logFileWriter = new FileWriter(_logFile, true);		    
		    }else{
			_logFileWriter = new FileWriter(_logFile, true);
			_logFileWriter.write("<html>\n<body>\n<h1>Udriver log file</h1>\n\n<p>\n<table>\n");
		    }
	    
		    _logEnabled = true;
		    add("Started logging to <strong>" + _logFile.getName() + "</strong>", OK, true);
		    
		}else{
		    add("No log file chosen; file logging disabled", WARNING, false);
		    _logEnabled = false;
		}
	    }else{
		add("File logging already started.", WARNING, false);
		System.out.println("You must first stop logging if you want to start it with another name");
	    }
	}
	catch(Exception e){
	    _close();
	    add(e.toString() + ". File logging disabled", WARNING, false);
	}
    }

    public void stopLog(){
	if(_logEnabled){

	    Date       date = new Date();
	    DateFormat df   = DateFormat.getDateTimeInstance(DateFormat.MEDIUM, DateFormat.MEDIUM);
	    add("Stopped logging to <strong>" + _logFile.getName() + "</strong>", OK, true);
	    if(_logEnabled){
		try {
		    _logFileWriter.close();
		    _logEnabled  = false;
		}
		catch(Exception e){
		    _close();
		    add(e.toString() + ". File logging disabled.", ERROR, false);
		}
	    }
	}else{
	    add("Cannot stop file logging which was not enabled", WARNING, false);
	}
    }

    public boolean loggingEnabled(){
	return _logEnabled;
    }

    private void _close(){
	_logEnabled = false;
	try {_logFileWriter.close(); } catch(Exception e){}
    }

    private String _bgcolor(int type){
	if(type == WARNING){
	    return " bgcolor=\"#FFA500\"";
	}else if(type == ERROR){
	    return " bgcolor=\"red\"";
	}else{
	    return "";
	}
    }

    /* Limits the number of rows in the internal buffer */
    public void limitRows(){
	int nrow = 0;
	int index = 0, nindex;
	while((nindex = _htmlBuffer.indexOf(START_ROW, index)) != -1){
	    nrow++;
	    index = nindex + 4;
	}
	if(nrow > MAX_ROW){
	    int start = _htmlBuffer.indexOf(START_ROW);
	    int end   = _htmlBuffer.indexOf(END_ROW);
	    if(end == -1){
		System.out.println("Error in logpanel: unterminated html table row");
	    }else{
		_htmlBuffer.delete(start, end+END_ROW.length());
	    }
	}
    }

}

