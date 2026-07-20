#ifndef	_SBI_TIMER_H
#define	_SBI_TIMER_H

void sbi_timer_init(void);
void sbi_timer_process(void);
int sbi_timer_has_expired(unsigned long mtimecmp, unsigned long current_time);
void clint_timer_event_start(unsigned long next_event);

#endif
