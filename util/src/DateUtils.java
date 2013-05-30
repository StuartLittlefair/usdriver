package warwick.marsh.util;
import java.util.Calendar;
import java.util.Date;
import java.text.SimpleDateFormat;

public final class DateUtils {
 
    public static final String DATE_FORMAT_NOW = "E,dd,MMM,yyyy HH:mm:ss zzz";

    public DateUtils() {
	
    }

    public static Date now() {
	Calendar cal = Calendar.getInstance();
	return cal.getTime();
    }
    
    public static Date parse(String data) throws Exception{
	SimpleDateFormat sdf = new SimpleDateFormat(DATE_FORMAT_NOW);
	return sdf.parse(data);
    }
    
    public static String form(Date date){
	SimpleDateFormat sdf = new SimpleDateFormat(DATE_FORMAT_NOW);
	return sdf.format(date);
    }
    
    public static double elapsed(Date date1){
	return (DateUtils.now().getTime()-date1.getTime())/1000.0;
    }
}
