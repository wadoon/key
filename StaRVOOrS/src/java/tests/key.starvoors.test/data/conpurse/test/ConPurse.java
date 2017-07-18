
public class ConPurse
{
  public ConPurse () {}

  public byte status;
  public final static byte Idle = 0;
  public final static short SW_IGNORED      = 0x6200;
  public final static short SW_SUCCESS      = 0x6150; 
  public static final boolean start_from_operation_log_full_ignored_at = true; 

  /*@ 
    @ public normal_behaviour
    @ requires start_from_operation_log_full_ignored_at && m == 1 && ( status == Idle && m == 2) ;
    @ ensures \result == SW_IGNORED;
    @ assignable \nothing;
    @ diverges true;
    @*/
  private short startFrom(int m)
  {    
    if (status == Idle)
    {             
         return SW_SUCCESS;
    }
    else return SW_IGNORED;
  }

}

