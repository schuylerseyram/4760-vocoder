/**
 *  V. Hunter Adams (vha3@cornell.edu)

    This is an experiment with the multicore capabilities on the
    RP2040. The program instantiates a timer interrupt on each core.
    Each of these timer interrupts writes to a separate channel
    of the SPI DAC and does DDS of two sine waves of two different
    frequencies. These sine waves are amplitude-modulated to "beeps."

    No spinlock is required to mediate the SPI writes because of the
    SPI buffer on the RP2040. Spinlocks are used in the main program
    running on each core to lock the other out from an incrementing
    global variable. These are "under the hood" of the PT_SEM_SAFE_x
    macros. Two threads ping-pong using these semaphores.

    Note that globals are visible from both cores. Note also that GPIO
    pin mappings performed on core 0 can be utilized from core 1.
    Creation of an alarm pool is required to force a timer interrupt to
    take place on core 1 rather than core 0.

 */

// Include the VGA grahics library
#include "vga_graphics.h"

#include "pico/divider.h"
// Include necessary libraries
#include <stdio.h>
#include <sys/time.h>
#include <math.h>
#include <string.h>
#include "pico/stdlib.h"
#include "pico/multicore.h"
#include "hardware/spi.h"
#include "hardware/sync.h"
#include "hardware/adc.h"
#include "hardware/pio.h"
#include "hardware/dma.h"
#include "hardware/clocks.h"
#include "hardware/pll.h"
// Include protothreads
#include "pt_cornell_rp2040_v1.h"

// Macros for fixed-point arithmetic (faster than floating point)
typedef signed int fix21;
#define multfix21(a, b) ((fix21)((((signed long long)(a)) * ((signed long long)(b))) >> 19))
#define float2fix21(a) ((fix21)((a) * 524288.0))
#define fix2float21(a) ((float)(a) / 524288.0)
#define absfix21(a) abs(a)
#define int2fix21(a) ((fix21)(a << 19))
#define fix2int21(a) ((int)(a >> 19))
#define char2fix21(a) (fix21)(((fix21)(a)) << 19)
#define divfix(a, b) (fix21)((((signed long long)(a)) << 19) / (b))

// Direct Digital Synthesis (DDS) parameters
#define two32 4294967296.0 // 2^32 (a constant)
#define Fs 8000            // sample rate
fix21 fixFs;
#define NUM_FILTERS 18

// the DDS units - core 0
// Phase accumulator and phase increment. Increment sets output frequency.
volatile unsigned int phase_accum_main_0[NUM_FILTERS] = {0,0,0,0,0,0,0,0};
volatile unsigned int phase_incr_main_0[NUM_FILTERS] = {0,0,0,0,0,0,0,0};

// DDS sine table (populated in main())
#define carrier_table_size 8192
int current_carrier;
fix21 sawtooth_carrier_table[carrier_table_size];
fix21 whitenoise_carrier_table[carrier_table_size];
fix21 triangle_carrier_table[carrier_table_size];

// Values output to DAC
int DAC_output_0;
int DAC_output_1;

// Amplitude modulation parameters and variables
fix21 max_amplitude = int2fix21(1); // maximum amplitude
fix21 attack_inc;                   // rate at which sound ramps up
fix21 decay_inc;                    // rate at which sound ramps down
fix21 current_amplitude_0 = 0;      // current amplitude (modified in ISR)
fix21 current_amplitude_1 = 0;      // current amplitude (modified in ISR)
fix21 sine_scale = 0;

// Timing parameters for beeps (units of interrupts)
#define ATTACK_TIME 200
#define DECAY_TIME 200
#define SUSTAIN_TIME 10000
#define BEEP_DURATION 10400
#define BEEP_REPEAT_INTERVAL 40000


// State machine variables
volatile unsigned int STATE_0 = 0;
volatile unsigned int count_0 = 0;

// SPI data
uint16_t DAC_data_1; // output value
uint16_t DAC_data_0; // output value

// DAC parameters (see the DAC datasheet)
// A-channel, 1x, active
#define DAC_config_chan_A 0b0011000000000000
// B-channel, 1x, active
#define DAC_config_chan_B 0b1011000000000000

// SPI configurations (note these represent GPIO number, NOT pin number)
#define PIN_MISO 4
#define PIN_CS 5
#define PIN_SCK 6
#define PIN_MOSI 7
#define LDAC 8
#define LED 25
#define SPI_PORT spi0

// Two variables to store core number
volatile int corenum_0;

// Global counter for spinlock experimenting
volatile int global_counter = 0;

fix21 lp_ysamp[NUM_FILTERS];
fix21 lp_ysig[NUM_FILTERS];

fix21 coefficients[NUM_FILTERS][2][5];

fix21 yy;
fix21 xn;
fix21 xn_1arrSamp[NUM_FILTERS];
fix21 xn_2arrSamp[NUM_FILTERS];
fix21 xn_1arrSig[NUM_FILTERS];
fix21 xn_2arrSig[NUM_FILTERS];
fix21 yn_1arrSamp[NUM_FILTERS];
fix21 yn_2arrSamp[NUM_FILTERS];
fix21 yn_1arrSig[NUM_FILTERS];
fix21 yn_2arrSig[NUM_FILTERS];

fix21 adc_data;
int current_amplitude;
int new_adc;


#define BASE_KEYPAD_PIN 9
#define KEYROWS 4
#define NUMKEYS 12
#define LED 25
// Keypad variables
unsigned int keycodes[12] = {0x28, 0x11, 0x21, 0x41, 0x12,
0x22, 0x42, 0x14, 0x24, 0x44,
0x18, 0x48};
unsigned int scancodes[4] = {0x01, 0x02, 0x04, 0x08};

char keytext[40];
int prev_key = 0;
unsigned int button = 0x70;
// States for debouncing FSM
enum state
{
NOT_PRESSED,
MAYBE_PRESSED,
MAYBE_NOT_PRESSED,
PRESSED
};
// Initial debouncing FSM state
int keypadState = NOT_PRESSED;
// Variable used in debouncing FSM
int possible = -1;
//list of center frequencies for the 18 bandpass filters which serve as frequencies for each of the 18 synthesizers
float carrier_freqs[NUM_FILTERS] = {50.0, 150.0, 250.0, 350.0, 450.0, 570.0, 700.0, 840.0, 1000.0,  1170.0, 1370.0, 1600.0, 1850.0, 2150.0, 2500.0, 2900.0};

float tenPercentIncrements[NUM_FILTERS] = {8.0, 10.0, 10.0, 10.0, 11.0, 12.0, 14.0, 15.0, 16.0, 19.0, 21.0, 24.0, 28.0, 32.0, 38.0, 45.0};

//========================================================
// Second order Butterworth bandpass
// xx is the current input signal sample
// b(1)*x(n)+b(2)*x(n-1)+b(3)*x(n-2) =
// b(1)*x(n)+0*b(1)*x(n-1)-b(1)*x(n-2) =
// b(1)* (x(n)-x(n-2))
uint32_t timed;

//co-efficients for the filters we used
const float float_coefficients[NUM_FILTERS][2][3] =

   {

        // filter 1 [20, 100)

        {

            // b coefficients b-low is first 2, b-high is second 2

            { 0.0305,         0,   -0.0305},

            // a coefficients

            { 1.0000,   -1.9379,    0.9391}


        },

        // filter 2 [100, 200)

        {

            // b coefficients b-low is first 2, b-high is second 2

            { 0.0378,         0,   -0.0378},

            // a coefficients

            {1.0000,   -1.9125,    0.9244}

        },

        // filter 3 [200, 300)

        {

            // b coefficients

            {0.0378,         0,   -0.0378},

            // a coefficients

            { 1.0000,   -1.8889,    0.9244}

        },

        // filter 4 [300, 400)

        {

            // b coefficients

            { 0.0378,         0,   -0.0378},

            // a coefficients

            {1.0000,   -1.8536,    0.9244}

        },

        // filter 5 [400, 510)

        {

            // b coefficients

            {0.0414,         0,   -0.0414},

            // a coefficients

            {1.0000,   -1.7977,    0.9171}

        },

        // filter 6 [510, 630)

        {

            // b coefficients

            {0.0450,         0,   -0.0450},

            // a coefficients

            {1.0000,   -1.7236,    0.9099}

        },

        // filter 7 [630, 770)

        {

            // b coefficients

            {0.0522,         0,   -0.0522},

            // a coefficients

            {1.0000,   -1.6188,    0.8957}


        },

        // filter 8 [770, 920)

        {

            // b coefficients

            {0.0557,         0,   -0.0557},

            // a coefficients

            {1.0000,   -1.4903,    0.8886}

        },

        // filter 9 [920 1080]

      {

            // b coefficients

            {0.0592,         0,   -0.0592},

            // a coefficients

            {1.0000,   -1.3331,    0.8816}

        },

        // filter 10 [1080 1270)

        {

            // b coefficients

            { 0.0696,         0,   -0.0696},

            // a coefficients

            {1.0000,   -1.1263,    0.8609}

        },

        // filter 11 [1270, 1480)

        {

            // b coefficients

            {0.0763,         0,   -0.0763},

            // a coefficients

            {1.0000,   -0.8738,    0.8473}

        },

        // filter 12 [1480, 1720)

        {

            // b coefficients

            { 0.0864,         0,   -0.0864},

            // a coefficients

            {1.0000,   -0.5672,    0.8273}

        },

        // filter 13 [1720, 2000)

        {

            // b coefficients

            {0.0994 ,        0  , -0.0994},

            // a coefficients

            {1.0000,   -0.1988 ,   0.8012}

        },

        // filter 14 [2000, 2320)

        {

            // b coefficients

            { 0.1122 ,        0  , -0.1122},

            // a coefficients

            {1.0000,    0.2243 ,   0.7757}

        },

        // filter 15 [2320, 2700)

        {

            // b coefficients

            {0.1307,         0 ,  -0.1307},

            // a coefficients

            { 1.0000 ,   0.6856   , 0.7386}

        },

        // filter 16 [2700, 3150)

        {

            // b coefficients

            {0.1515 ,        0 ,  -0.1515},

            // a coefficients

            {1.0000,    1.1450  ,  0.6970}

        },

        //filter 17 [3150 3700]
        {
            {0.1799,        0,   -0.1799},
            { 1.0000,    1.5108,    0.6401}
        },

        //filter 18 [3700 3999]
        {
            {0.1055,         0 ,  -0.1055},
            { 1.0000,    1.7888 ,   0.7890}
        }

   };





fix21 Butter2band(fix21 xx, fix21 b1, fix21 a2, fix21 a3, fix21 *xn_2, fix21 *xn_1, fix21 *yn_2, fix21 *yn_1)
{
    yy = multfix21((xx-*xn_2), b1);
    *xn_2 = *xn_1;
    *xn_1 = xx;
    yy = yy - multfix21(*yn_2, a3);
    *yn_2 = *yn_1;
    yy = yy - multfix21(*yn_1, a2);
    *yn_1 = yy;
    return yy;
}

fix21 lowpass(fix21 x, fix21 *lp_y1)
{
    fix21 lp_yy = x + ((*lp_y1 - x) - ((*lp_y1 - x) >> 8));
    // fix21 lp_yy = x + ((*lp_y1 - x)>>6);
    *lp_y1 = lp_yy;
    return lp_yy;
}

// This timer ISR is called on core 0
// Use this time for getting inputs from the ADC at a sampling rate of 8kHz
bool repeating_timer_callback_core_0(struct repeating_timer *t)
{

        // struct timeval tv;
    // gettimeofday(&tv, NULL);
    // long long micros = tv.tv_sec * 1000000LL + tv.tv_usec;

    // Sample ADC once
    uint16_t result = adc_read();
    adc_data = int2fix21((int)result);
     new_adc = 1;

    // DAC_output_0 = fix2int21(lowpass(absfix21(adc_data), &(lp_ysamp[0])));

    // printf("Raw value: %d", result);

    // first generate a synthesized carrier sample
   

    DAC_output_0 = current_amplitude;
   
    // Mask with DAC control bits
    DAC_data_0 = (DAC_config_chan_B | (DAC_output_0 & 0xffff));

    // SPI write (no spinlock b/c of SPI buffer)
    spi_write16_blocking(SPI_PORT, &DAC_data_0, 1);
    // printf("DAC output: %d", DAC_output_0);
    

    // retrieve core number of execution
    corenum_0 = get_core_num();

    return true;
}


static PT_THREAD(protothread_vocoder(struct pt *pt)) 
{
    PT_BEGIN(pt);
    while(1)
    {

        PT_YIELD_UNTIL(pt, new_adc == 1);
         uint32_t start_time = time_us_32();
        fix21 adcd = adc_data;

        new_adc = 0;

    //fix21 carrier_sample = carrier_table[phase_accum_main_0];

    fix21 y = 0;

    int i;

    // Now, apply bandpass filters to ADC sample
    for (i = 0; i < NUM_FILTERS; i++)
    {
          fix21 carrier_sample;
        phase_accum_main_0[i] = (phase_accum_main_0[i] + phase_incr_main_0[i]) % carrier_table_size;
        if(current_carrier == 1) {
            carrier_sample = sawtooth_carrier_table[phase_accum_main_0[i]];
        } else if(current_carrier == 2) {
            carrier_sample = whitenoise_carrier_table[phase_accum_main_0[i]];
        } else if(current_carrier == 3) {
            carrier_sample = triangle_carrier_table[phase_accum_main_0[i]];
        }

        fix21 sample = Butter2band(adcd, coefficients[i][0][0], coefficients[i][1][1], coefficients[i][1][2], 
            &(xn_2arrSamp[i]), &(xn_1arrSamp[i]), &(yn_2arrSamp[i]), &(yn_1arrSamp[i]));
        fix21 amplifiedSample = lowpass(absfix21(sample), &(lp_ysamp[i]));
        fix21 filteredSig = Butter2band(carrier_sample, coefficients[i][0][0], coefficients[i][1][1], coefficients[i][1][2],  
             &(xn_2arrSig[i]), &(xn_1arrSig[i]),  &(yn_2arrSig[i]), &(yn_1arrSig[i]));
        fix21 amplifiedSig = lowpass(absfix21(filteredSig), &(lp_ysig[i]));
        y += amplifiedSig != 0 ? multfix21(filteredSig, divfix(amplifiedSample, amplifiedSig))  : 0;
        //printf("sample: %f", sample);
        //y += sample;
    }

    current_amplitude = (int)((y >> 20) + 2048);
   timed = time_us_32() - start_time;

     //printf("time: %d", current_amplitude);
    }
    PT_END(pt);
}

static PT_THREAD(protothread_core_1(struct pt *pt))
{
    // Indicate thread beginning
    PT_BEGIN(pt);
    // Some variables
    static int i;
    static uint32_t keypad;
    while (1)
    {
        setTextColor(MAGENTA);
        setCursor(200, 0);
        setTextSize(3);
        writeString("Voice Manipulator");
        setTextColor(RED);
        setCursor(25, 50);
        setTextSize(2);
        writeString("Press 1 for Sawtooth Wave");
        setCursor(25, 75);
        setTextColor(WHITE);
        writeString("Press 2 for White Noise");
        setCursor(25,100);
        setTextColor(BLUE);
        writeString("Press 3 for Triangle Wave");
        setCursor(25, 125);
        setTextColor(GREEN);
        writeString("Press 4 to increase pitch");
        setCursor(25, 150);
        setTextColor(YELLOW);
        writeString("Press 5 to lower pitch");
         setCursor(300, 300);
    setTextColor(WHITE);
     setTextColor2(7,0);
     setTextSize(2);
     writeString("Time spent: ");
     char dest[41];
     sprintf(dest, "%d", timed);
     writeString(dest);
        

        // Scan the keypad!
        for (i = 0; i < KEYROWS; i++)
        {
            // Set a row high
            gpio_put_masked((0xF << BASE_KEYPAD_PIN), (scancodes[i] << BASE_KEYPAD_PIN));
            // Small delay required
            sleep_us(1);
            // Read the keycode
            keypad = ((gpio_get_all() >> BASE_KEYPAD_PIN) & 0x7F);
            // Break if button(s) are pressed
            if (keypad & button) {
                break;
            }
        }
        // If we found a button . . .
        if (keypad & button)
        {
            // Look for a valid keycode.
            for (i = 0; i < NUMKEYS; i++)
            {
                if (keypad == keycodes[i]) {
                    break;
                }
            }
            // If we don’t find one, report invalid keycode
            if (i == NUMKEYS) {
                (i = -1);
            }
        }
        // Otherwise, indicate invalid/non-pressed buttons
        else {
            (i = -1);
        }
        // Start of the debouncing FSM
        switch (keypadState)
        {
        case NOT_PRESSED:
        // If state is not pressed only take action on a potential key press (not a -1)
            if (i != -1)
            {
                keypadState = MAYBE_PRESSED;
                possible = i;
            }
            break;
        case MAYBE_PRESSED:
        // If state is maybe pressed and we receive the same key press that possible holds state becomes pressed
            if (i != -1 && i == possible)
            {
                keypadState = PRESSED;
                // 
               // carrier_freq = carrier_freqs[i-1];

                if(i == 1) {
                    current_carrier = 1;
                }
                if(i == 2) {
                    current_carrier = 2;
                }
                if(i == 3) {
                    current_carrier = 3;
                }
                if(i == 4) {
                    int j;
                    for(j = 0; j < NUM_FILTERS; j++) {
                        carrier_freqs[j] = carrier_freqs[j] + tenPercentIncrements[j];
                        phase_incr_main_0[j] = (carrier_freqs[j] * carrier_table_size) / Fs;
                    }
                }
                if(i == 5) {
                    int j;
                    for(j = 0; j < NUM_FILTERS; j++) {
                        carrier_freqs[j] = carrier_freqs[j] - tenPercentIncrements[j];
                        phase_incr_main_0[j] = (carrier_freqs[j] * carrier_table_size) / Fs;

                    }
                }
                // setTextColor2(7,0);
                // setCursor(65, 0);
                // setTextSize(2);
                // writeString("Carrier Frequency: ");
                // char dest[41];
                // sprintf(dest, "%f", carrier_freq);
                // writeString(dest);
            }
        // State transition if the key press does not match what is in possible
            else
            {
                keypadState = NOT_PRESSED;
                possible = -1;
            }
            break;
        case PRESSED:
        // If state is pressed only take action on a key press different than possible
            if (i != possible)
            {
                keypadState = MAYBE_NOT_PRESSED;
            }
            break;
        case MAYBE_NOT_PRESSED:
        // If the last two key reads are different from possible we are not pressed
            if (i != possible)
            {
                keypadState = NOT_PRESSED;
                possible = -1;
            }
        // If key press matches possible then key is pressed again
            else
            {
                keypadState = PRESSED;
            }
        }

        PT_YIELD_usec(30000);
    }
    PT_END(pt);
}


void core1_main(){
  // Add animation thread
  pt_add_thread(protothread_core_1);
  // Start the scheduler
  pt_schedule_start ;

}



// Core 0 entry point
int main()
{
    // Initialize stdio/uart (printf won't work unless you do this!)
    stdio_init_all();
    printf("Hello, friends!\n");

    int i;
    int j;
    int k;
    // convert float coefficients to fixed point
    for (i = 0; i < NUM_FILTERS; i++)
    {
        for (j = 0; j < 2; j++)
        {
            for (k = 0; k < 3; k++)
            {
                coefficients[i][j][k] = float2fix21(float_coefficients[i][j][k]);
            }
        }
    }

    int h;
    for(h = 0; h < NUM_FILTERS; h++) {
        phase_incr_main_0[h] = (carrier_freqs[h] * carrier_table_size) / Fs;
    }

    // Initialize SPI channel (channel, baud rate set to 20MHz)
    spi_init(SPI_PORT, 20000000);
    // Format (channel, data bits per transfer, polarity, phase, order)
    spi_set_format(SPI_PORT, 16, 0, 0, 0);

    // Map SPI signals to GPIO ports
    gpio_set_function(PIN_MISO, GPIO_FUNC_SPI);
    gpio_set_function(PIN_SCK, GPIO_FUNC_SPI);
    gpio_set_function(PIN_MOSI, GPIO_FUNC_SPI);
    gpio_set_function(PIN_CS, GPIO_FUNC_SPI);

    // Map LDAC pin to GPIO port, hold it low (could alternatively tie to GND)
    gpio_init(LDAC);
    gpio_set_dir(LDAC, GPIO_OUT);
    gpio_put(LDAC, 0);

    // Map LED to GPIO port, make it low
    gpio_init(LED);
    gpio_set_dir(LED, GPIO_OUT);
    gpio_put(LED, 0);


     // start core 1 
    multicore_reset_core1();
    multicore_launch_core1(&core1_main);

    // set up increments for calculating bow envelope
    attack_inc = divfix(max_amplitude, int2fix21(ATTACK_TIME));
    decay_inc = divfix(max_amplitude, int2fix21(DECAY_TIME));

    // Build the sine lookup table for a sawtooth carrier wave
    // scaled to produce values between 0 and 4096 (for 12-bit DAC)
    int ii;
    for (ii = 0; ii < carrier_table_size; ii++)
    {
         //sawtooth
         sawtooth_carrier_table[ii] = float2fix21( ((float)ii) / (carrier_table_size - 1));
        //sine wave
       // carrier_table[ii] = float2fix21(0.5 + 0.5 * sin((2 * M_PI * ii) / carrier_table_size));
        //pulse 
        //carrier_table[ii] = float2fix21(ii < 4096 ? 1.0 : 0.0);
        //square
         if(ii < 4096) {
             triangle_carrier_table[ii] = float2fix21(ii * (1.0 / 4096.0));
         } else {
        triangle_carrier_table[ii] = float2fix21(1.0 - (ii - 4096) * (1.0/4096));
         }

        //white noise
        whitenoise_carrier_table[ii] = float2fix21(((rand() % 100) / 100.0));
    }

    current_carrier = 1;

    // yy = 0;
    // xn = 0;
    // xn_1 = 0;
    // xn_2 = 0;
    // xn_3 = 0;
    // xn_4 = 0;
    // yn_1 = 0;
    // yn_2 = 0;
    // yn_3 = 0;
    // yn_4 = 0;
    current_amplitude = 0;
  new_adc = 0;
    adc_data = 0;

    // ADC setup
    adc_init();
    adc_gpio_init(26);

    initVGA() ;
    setTextColor(WHITE);
    setCursor(65, 0);
    setTextSize(2);
    //writeString("Carrier Frequency: ");
    char dest[41];
    //sprintf(dest, "%f", carrier_freq);
   // writeString(dest);
    adc_select_input(0);

    // Create a repeating timer that calls
    // repeating_timer_callback (defaults core 0)
    struct repeating_timer timer_core_0;

    // Negative delay so means we will call repeating_timer_callback, and call it
    // again 125us (8kHz) later regardless of how long the callback took to execute
    add_repeating_timer_us(-125,
                           repeating_timer_callback_core_0, NULL, &timer_core_0);

    // Add core 0 threads
     pt_add_thread(protothread_vocoder);


     gpio_init_mask((0x7F << BASE_KEYPAD_PIN));
    // Set row-pins to output
    gpio_set_dir_out_masked((0xF << BASE_KEYPAD_PIN));
    // Set all output pins to low
    gpio_put_masked((0xF << BASE_KEYPAD_PIN), (0x0 <<
        BASE_KEYPAD_PIN));
    // Turn on pulldown resistors for column pins (on by default)
    gpio_pull_down((BASE_KEYPAD_PIN + 4));
    gpio_pull_down((BASE_KEYPAD_PIN + 5));
    gpio_pull_down((BASE_KEYPAD_PIN + 6));

    // Start scheduling core 0 threads
    pt_schedule_start;
}

