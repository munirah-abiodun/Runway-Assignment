/* Copyright (c) 2025 Trevor Bakker
*
* This program is free software: you can redistribute it and/or modify
* it under the terms of the GNU General Public License as published by
* the Free Software Foundation, either version 3 of the License, or
* (at your option) any later version.
*
* This program is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILTY or FITNESS FOR A PARTICULAR PURPOSE.  See the
* GNU General Public License for more details.
*
* You should have received a copy of the GNU General Public License
* along with this program.  If not, see <http://www.gnu.org/license/>.
*/
 
#include <pthread.h>
#include <semaphore.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <assert.h>
#include <time.h>

/*** Constants that define parameters of the simulation ***/

#define MAX_RUNWAY_CAPACITY 2    /* Number of aircraft that can use runway simultaneously */
#define CONTROLLER_LIMIT 8       /* Number of aircraft the controller can manage before break */
#define MAX_AIRCRAFT 1000        /* Maximum number of aircraft in the simulation */
#define FUEL_MIN 20              /* Minimum fuel reserve in seconds */
#define FUEL_MAX 60              /* Maximum fuel reserve in seconds */
#define EMERGENCY_TIMEOUT 30     /* Max wait time for emergency aircraft in seconds */
#define DIRECTION_SWITCH_TIME 5  /* Time required to switch runway direction */
#define DIRECTION_LIMIT 3        /* Max consecutive aircraft in same direction */

#define COMMERCIAL 0
#define CARGO 1
#define EMERGENCY 2

#define NORTH 0
#define SOUTH 1
#define EAST  2
#define WEST  4

/* TODO */
/* Add your synchronization variables here */

/* basic information about simulation.  they are printed/checked at the end 
 * and in assert statements during execution.
 *
 * you are responsible for maintaining the integrity of these variables in the 
 * code that you develop. 
 */
 pthread_mutex_t runway_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t runway_available = PTHREAD_COND_INITIALIZER;

static int aircraft_on_runway = 0;       /* Total number of aircraft currently on runway */
static int commercial_on_runway = 0;     /* Total number of commercial aircraft on runway */
static int cargo_on_runway = 0;          /* Total number of cargo aircraft on runway */
static int emergency_on_runway = 0;      /* Total number of emergency aircraft on runway */
static int aircraft_since_break = 0;     /* Aircraft processed since last controller break */
static int current_direction = NORTH;    /* Current runway direction (NORTH or SOUTH) */
static int consecutive_direction = 0;    /* Consecutive aircraft in current direction */


typedef struct 
{
  int arrival_time;         // time between the arrival of this aircraft and the previous aircraft
  int runway_time;          // time the aircraft needs to spend on the runway
  int aircraft_id;
  int aircraft_type;        // COMMERCIAL, CARGO, or EMERGENCY
  int fuel_reserve;         // Randomly assigned fuel reserve (FUEL_MIN to FUEL_MAX seconds)
  time_t arrival_timestamp; // timestamp when aircraft thread was created
} aircraft_info;

/* Called at beginning of simulation.  
 * TODO: Create/initialize all synchronization
 * variables and other global variables that you add.
 */
static int initialize(aircraft_info *ai, char *filename) 
{
  aircraft_on_runway    = 0;
  commercial_on_runway  = 0;
  cargo_on_runway       = 0;
  emergency_on_runway   = 0;
  aircraft_since_break  = 0;
  current_direction     = NORTH;
  consecutive_direction = 0;

  /* Initialize your synchronization variables (and 
   * other variables you might use) here
   */

  /* seed random number generator for fuel reserves */
  srand(time(NULL));

  /* Read in the data file and initialize the aircraft array */
  FILE *fp;

  if((fp=fopen(filename, "r")) == NULL) 
  {
    printf("Cannot open input file %s for reading.\n", filename);
    exit(1);
  }

  int i = 0;
  char line[256];
  while (fgets(line, sizeof(line), fp) && i < MAX_AIRCRAFT) 
  {
    /* Skip comment lines and empty lines */
    if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') {
      continue;
    }
    
    /* Parse the line */
    if (sscanf(line, "%d%d%d", &(ai[i].aircraft_type), &(ai[i].arrival_time), 
               &(ai[i].runway_time)) == 3) {
      /* Assign random fuel reserve between FUEL_MIN and FUEL_MAX */
      ai[i].fuel_reserve = FUEL_MIN + (rand() % (FUEL_MAX - FUEL_MIN + 1));
      i = i + 1;
    }
  }

  fclose(fp);
  return i;
}

/* Code executed by controller to simulate taking a break 
 * You do not need to add anything here.  
 */
__attribute__((unused)) static void take_break() 
{
  printf("The air traffic controller is taking a break now.\n");
  sleep(5);
  assert( aircraft_on_runway == 0 );
  aircraft_since_break = 0;
}

/* Code executed to switch runway direction
 * You do not need to add anything here.
 */
__attribute__((unused)) static void switch_direction()
{
  printf("Switching runway direction from %s to %s\n",
         current_direction == NORTH ? "NORTH" : "SOUTH",
         current_direction == NORTH ? "SOUTH" : "NORTH");
  
  assert( aircraft_on_runway == 0 );  // Runway must be empty to switch
  
  sleep(DIRECTION_SWITCH_TIME);
  
  current_direction = (current_direction == NORTH) ? SOUTH : NORTH;
  consecutive_direction = 0;
  
  printf("Runway direction switched to %s\n",
         current_direction == NORTH ? "NORTH" : "SOUTH");
}

/* Code for the air traffic controller thread. This is fully implemented except for 
 * synchronization with the aircraft. See the comments within the function for details.
 */
void *controller_thread(void *arg) 
{
  // Suppress the warning for now
 (void)arg;

  printf("The air traffic controller arrived and is beginning operations\n");

  /* Loop while waiting for aircraft to arrive. */
  while (1) 
  {
    /* TODO */
    /* Add code here to handle aircraft requests, controller breaks,      */
    /* and runway direction switches.                                     */
    /* Currently the body of the loop is empty.  There's no communication */
    /* between controller and aircraft, i.e. all aircraft are admitted    */
    /* without regard for runway capacity, aircraft type, direction,      */
    /* priorities, and whether the controller needs a break.              */
    /* You need to add all of this.                                       */
    
    /* Allow thread to be cancelled */
    pthread_testcancel();
    usleep(100000); // 100ms sleep to prevent busy waiting
  }
  pthread_exit(NULL);
}


/* Code executed by a commercial aircraft to enter the runway.
 * You have to implement this.  Do not delete the assert() statements,
 * but feel free to add your own.
 */
void commercial_enter(aircraft_info *arg) 
{
  // Suppress the compiler warning
  (void)arg;

 pthread_mutex_lock(&runway_mutex);
  
  while (aircraft_on_runway >= MAX_RUNWAY_CAPACITY) {
    printf("Commercial aircraft %d waiting - runway at capacity (%d/%d)\n", 
           arg->aircraft_id, aircraft_on_runway, MAX_RUNWAY_CAPACITY);
    pthread_cond_wait(&runway_available, &runway_mutex);
  }
  
  aircraft_on_runway = aircraft_on_runway + 1;
  aircraft_since_break = aircraft_since_break + 1;
  commercial_on_runway = commercial_on_runway + 1;
  consecutive_direction = consecutive_direction + 1;
  
  printf("Commercial aircraft %d entered runway. Aircraft on runway: %d\n", 
         arg->aircraft_id, aircraft_on_runway);
  
  pthread_mutex_unlock(&runway_mutex);
}

/* Code executed by a cargo aircraft to enter the runway.
 * You have to implement this.  Do not delete the assert() statements,
 * but feel free to add your own.
 */
void cargo_enter(aircraft_info *ai) 
{
  (void)ai;

   pthread_mutex_lock(&runway_mutex);
  
  while (aircraft_on_runway >= MAX_RUNWAY_CAPACITY) {
    printf("Cargo aircraft %d waiting - runway at capacity (%d/%d)\n", 
           ai->aircraft_id, aircraft_on_runway, MAX_RUNWAY_CAPACITY);
    pthread_cond_wait(&runway_available, &runway_mutex);
  }
  
  aircraft_on_runway = aircraft_on_runway + 1;
  aircraft_since_break = aircraft_since_break + 1;
  cargo_on_runway = cargo_on_runway + 1;
  consecutive_direction = consecutive_direction + 1;
  
  printf("Cargo aircraft %d entered runway. Aircraft on runway: %d\n", 
         ai->aircraft_id, aircraft_on_runway);
  
  pthread_mutex_unlock(&runway_mutex);

}

/* Code executed by an emergency aircraft to enter the runway.
 * You have to implement this.  Do not delete the assert() statements,
 * but feel free to add your own.
 */
void emergency_enter(aircraft_info *ai) 
{
  (void)ai;

   pthread_mutex_lock(&runway_mutex);
  
  // REQUIREMENT 1: Wait if runway is at capacity (2 aircraft)
  while (aircraft_on_runway >= MAX_RUNWAY_CAPACITY) {
    printf("EMERGENCY aircraft %d waiting - runway at capacity (%d/%d)\n", 
           ai->aircraft_id, aircraft_on_runway, MAX_RUNWAY_CAPACITY);
    pthread_cond_wait(&runway_available, &runway_mutex);
  }
  
  // Enter the runway
  aircraft_on_runway = aircraft_on_runway + 1;
  aircraft_since_break = aircraft_since_break + 1;
  emergency_on_runway = emergency_on_runway + 1;
  consecutive_direction = consecutive_direction + 1;
  
  printf("EMERGENCY aircraft %d entered runway. Aircraft on runway: %d\n", 
         ai->aircraft_id, aircraft_on_runway);
  
  pthread_mutex_unlock(&runway_mutex);
}

/* Code executed by an aircraft to simulate the time spent on the runway
 * You do not need to add anything here.  
 */
static void use_runway(int t) 
{
  sleep(t);
}


/* Code executed by a commercial aircraft when leaving the runway.
 * You need to implement this.  Do not delete the assert() statements,
 * but feel free to add as many of your own as you like.
 */
static void commercial_leave() 
{
 pthread_mutex_lock(&runway_mutex);
  
  aircraft_on_runway = aircraft_on_runway - 1;
  commercial_on_runway = commercial_on_runway - 1;
  
  printf("Commercial aircraft left. Aircraft on runway: %d\n", aircraft_on_runway);
  
  // REQUIREMENT 1: Signal waiting aircraft that space is available
  pthread_cond_signal(&runway_available);
  
  pthread_mutex_unlock(&runway_mutex);
}

/* Code executed by a cargo aircraft when leaving the runway.
 * You need to implement this.  Do not delete the assert() statements,
 * but feel free to add as many of your own as you like.
 */
static void cargo_leave() 
{
  pthread_mutex_lock(&runway_mutex);
  
  aircraft_on_runway = aircraft_on_runway - 1;
  cargo_on_runway = cargo_on_runway - 1;
  
  printf("Cargo aircraft left. Aircraft on runway: %d\n", aircraft_on_runway);
  
  // REQUIREMENT 1: Signal waiting aircraft that space is available
  pthread_cond_signal(&runway_available);
  
  pthread_mutex_unlock(&runway_mutex);
}

/* Code executed by an emergency aircraft when leaving the runway.
 * You need to implement this.  Do not delete the assert() statements,
 * but feel free to add as many of your own as you like.
 */
static void emergency_leave() 
{
 pthread_mutex_lock(&runway_mutex);
  
  aircraft_on_runway = aircraft_on_runway - 1;
  emergency_on_runway = emergency_on_runway - 1;
  
  printf("EMERGENCY aircraft left. Aircraft on runway: %d\n", aircraft_on_runway);
  
  // REQUIREMENT 1: Signal waiting aircraft that space is available
  pthread_cond_signal(&runway_available);
  
  pthread_mutex_unlock(&runway_mutex);
}

/* Main code for commercial aircraft threads.  
 * You do not need to change anything here, but you can add
 * debug statements to help you during development/debugging.
 */
void* commercial_aircraft(void *ai_ptr) 
{
  aircraft_info *ai = (aircraft_info*)ai_ptr;
  
  /* Record arrival time for fuel tracking */
  ai->arrival_timestamp = time(NULL);

  /* Request runway access */
  commercial_enter(ai);

  printf("Commercial aircraft %d (fuel: %ds) is now on the runway (direction: %s)\n", 
         ai->aircraft_id, ai->fuel_reserve,
         current_direction == NORTH ? "NORTH" : "SOUTH");

  assert(aircraft_on_runway <= MAX_RUNWAY_CAPACITY && aircraft_on_runway >= 0);
  assert(commercial_on_runway >= 0 && commercial_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(cargo_on_runway >= 0 && cargo_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(emergency_on_runway >= 0 && emergency_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(cargo_on_runway == 0 ); // Commercial and cargo cannot mix
  
  /* Use runway  --- do not make changes to the 3 lines below*/
  printf("Commercial aircraft %d begins runway operations for %d seconds\n", 
         ai->aircraft_id, ai->runway_time);
  use_runway(ai->runway_time);
  printf("Commercial aircraft %d completes runway operations and prepares to depart\n", 
         ai->aircraft_id);

  /* Leave runway */
  commercial_leave();  

  printf("Commercial aircraft %d has cleared the runway\n", ai->aircraft_id);

  if (!(aircraft_on_runway <= MAX_RUNWAY_CAPACITY && aircraft_on_runway >= 0)) {
    printf("ASSERT FAILURE: aircraft_on_runway=%d (should be 0-%d)\n", aircraft_on_runway, MAX_RUNWAY_CAPACITY);
    printf("Runway state: commercial=%d, cargo=%d, emergency=%d, direction=%s\n", 
           commercial_on_runway, cargo_on_runway, emergency_on_runway,
           current_direction == NORTH ? "NORTH" : "SOUTH");
  }
  assert(aircraft_on_runway <= MAX_RUNWAY_CAPACITY && aircraft_on_runway >= 0);
  assert(commercial_on_runway >= 0 && commercial_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(cargo_on_runway >= 0 && cargo_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(emergency_on_runway >= 0 && emergency_on_runway <= MAX_RUNWAY_CAPACITY);

  pthread_exit(NULL);
}

/* Main code for cargo aircraft threads.
 * You do not need to change anything here, but you can add
 * debug statements to help you during development/debugging.
 */
void* cargo_aircraft(void *ai_ptr) 
{
  aircraft_info *ai = (aircraft_info*)ai_ptr;
  
  /* Record arrival time for fuel tracking */
  ai->arrival_timestamp = time(NULL);

  /* Request runway access */
  cargo_enter(ai);

  printf("Cargo aircraft %d (fuel: %ds) is now on the runway (direction: %s)\n", 
         ai->aircraft_id, ai->fuel_reserve,
         current_direction == NORTH ? "NORTH" : "SOUTH");

  if (!(aircraft_on_runway <= MAX_RUNWAY_CAPACITY && aircraft_on_runway >= 0)) {
    printf("ASSERT FAILURE: aircraft_on_runway=%d (should be 0-%d)\n", aircraft_on_runway, 
            MAX_RUNWAY_CAPACITY);
    printf("Runway state: commercial=%d, cargo=%d, emergency=%d, direction=%s\n", 
           commercial_on_runway, cargo_on_runway, emergency_on_runway,
           current_direction == NORTH ? "NORTH" : "SOUTH");
  }
  assert(aircraft_on_runway <= MAX_RUNWAY_CAPACITY && aircraft_on_runway >= 0);
  assert(commercial_on_runway >= 0 && commercial_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(cargo_on_runway >= 0 && cargo_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(emergency_on_runway >= 0 && emergency_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(commercial_on_runway == 0 ); 

  printf("Cargo aircraft %d begins runway operations for %d seconds\n", 
         ai->aircraft_id, ai->runway_time);
  use_runway(ai->runway_time);
  printf("Cargo aircraft %d completes runway operations and prepares to depart\n", 
         ai->aircraft_id);

  /* Leave runway */
  cargo_leave();        

  printf("Cargo aircraft %d has cleared the runway\n", ai->aircraft_id);

  if (!(aircraft_on_runway <= MAX_RUNWAY_CAPACITY && aircraft_on_runway >= 0)) {
    printf("ASSERT FAILURE: aircraft_on_runway=%d (should be 0-%d)\n", 
           aircraft_on_runway, MAX_RUNWAY_CAPACITY);
    printf("Runway state: commercial=%d, cargo=%d, emergency=%d, direction=%s\n", 
           commercial_on_runway, cargo_on_runway, emergency_on_runway,
           current_direction == NORTH ? "NORTH" : "SOUTH");
  }
  assert(aircraft_on_runway <= MAX_RUNWAY_CAPACITY && aircraft_on_runway >= 0);
  assert(commercial_on_runway >= 0 && commercial_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(cargo_on_runway >= 0 && cargo_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(emergency_on_runway >= 0 && emergency_on_runway <= MAX_RUNWAY_CAPACITY);

  pthread_exit(NULL);
}

/* Main code for emergency aircraft threads.
 * You do not need to change anything here, but you can add
 * debug statements to help you during development/debugging.
 */
void* emergency_aircraft(void *ai_ptr) 
{
  aircraft_info *ai = (aircraft_info*)ai_ptr;
  
  /* Record arrival time for fuel and emergency timeout tracking */
  ai->arrival_timestamp = time(NULL);

  /* Request runway access */
  emergency_enter(ai);

  printf("EMERGENCY aircraft %d (fuel: %ds) is now on the runway (direction: %s)\n", 
         ai->aircraft_id, ai->fuel_reserve,
         current_direction == NORTH ? "NORTH" : "SOUTH");

  if (!(aircraft_on_runway <= MAX_RUNWAY_CAPACITY && aircraft_on_runway >= 0)) {
    printf("ASSERT FAILURE: aircraft_on_runway=%d (should be 0-%d)\n", aircraft_on_runway, 
            MAX_RUNWAY_CAPACITY);
    printf("Runway state: commercial=%d, cargo=%d, emergency=%d, direction=%s\n", 
           commercial_on_runway, cargo_on_runway, emergency_on_runway,
           current_direction == NORTH ? "NORTH" : "SOUTH");
  }
  assert(aircraft_on_runway <= MAX_RUNWAY_CAPACITY && aircraft_on_runway >= 0);
  assert(commercial_on_runway >= 0 && commercial_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(cargo_on_runway >= 0 && cargo_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(emergency_on_runway >= 0 && emergency_on_runway <= MAX_RUNWAY_CAPACITY);

  printf("EMERGENCY aircraft %d begins runway operations for %d seconds\n", 
         ai->aircraft_id, ai->runway_time);
  use_runway(ai->runway_time);
  printf("EMERGENCY aircraft %d completes runway operations and prepares to depart\n", 
         ai->aircraft_id);

  /* Leave runway */
  emergency_leave();        

  printf("EMERGENCY aircraft %d has cleared the runway\n", ai->aircraft_id);

  if (!(aircraft_on_runway <= MAX_RUNWAY_CAPACITY && aircraft_on_runway >= 0)) {
    printf("ASSERT FAILURE: aircraft_on_runway=%d (should be 0-%d)\n", 
           aircraft_on_runway, MAX_RUNWAY_CAPACITY);
    printf("Runway state: commercial=%d, cargo=%d, emergency=%d, direction=%s\n", 
           commercial_on_runway, cargo_on_runway, emergency_on_runway,
           current_direction == NORTH ? "NORTH" : "SOUTH");
  }
  assert(aircraft_on_runway <= MAX_RUNWAY_CAPACITY && aircraft_on_runway >= 0);
  assert(commercial_on_runway >= 0 && commercial_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(cargo_on_runway >= 0 && cargo_on_runway <= MAX_RUNWAY_CAPACITY);
  assert(emergency_on_runway >= 0 && emergency_on_runway <= MAX_RUNWAY_CAPACITY);

  pthread_exit(NULL);
}

/* Main function sets up simulation and prints report
 * at the end.
 * GUID: 355F4066-DA3E-4F74-9656-EF8097FBC985
 */
int main(int nargs, char **args) 
{
  int i;
  int result;
  int num_aircraft;
  void *status;
  pthread_t controller_tid;
  pthread_t aircraft_tid[MAX_AIRCRAFT];
  aircraft_info ai[MAX_AIRCRAFT];

  if (nargs != 2) 
  {
    printf("Usage: runway <name of inputfile>\n");
    return EINVAL;
  }

  num_aircraft = initialize(ai, args[1]);
  if (num_aircraft > MAX_AIRCRAFT || num_aircraft <= 0) 
  {
    printf("Error:  Bad number of aircraft threads. "
           "Maybe there was a problem with your input file?\n");
    return 1;
  }

  printf("Starting runway simulation with %d aircraft ...\n", num_aircraft);

  result = pthread_create(&controller_tid, NULL, controller_thread, NULL);

  if (result) 
  {
    printf("runway:  pthread_create failed for controller: %s\n", strerror(result));
    exit(1);
  }

  for (i=0; i < num_aircraft; i++) 
  {
    ai[i].aircraft_id = i;
    sleep(ai[i].arrival_time);
                
    if (ai[i].aircraft_type == COMMERCIAL)
    {
      result = pthread_create(&aircraft_tid[i], NULL, commercial_aircraft, 
                             (void *)&ai[i]);
    }
    else if (ai[i].aircraft_type == CARGO)
    {
      result = pthread_create(&aircraft_tid[i], NULL, cargo_aircraft, 
                             (void *)&ai[i]);
    }
    else 
    {
      result = pthread_create(&aircraft_tid[i], NULL, emergency_aircraft, 
                             (void *)&ai[i]);
    }

    if (result) 
    {
      printf("runway: pthread_create failed for aircraft %d: %s\n", 
            i, strerror(result));
      exit(1);
    }
  }

  /* wait for all aircraft threads to finish */
  for (i = 0; i < num_aircraft; i++) 
  {
    pthread_join(aircraft_tid[i], &status);
  }

  /* tell the controller to finish. */
  pthread_cancel(controller_tid);
  pthread_join(controller_tid, &status);

  printf("Runway simulation done.\n");

  return 0;
}
